;;;-*- Mode:Lisp; Syntax:Common-Lisp; Package:CHAOS -*-
;;;
;;; Copyright (c) 2000-2015, Toshimi Sawada. All rights reserved.
;;;
;;; Redistribution and use in source and binary forms, with or without
;;; modification, are permitted provided that the following conditions
;;; are met:
;;;
;;;   * Redistributions of source code must retain the above copyright
;;;     notice, this list of conditions and the following disclaimer.
;;;
;;;   * Redistributions in binary form must reproduce the above
;;;     copyright notice, this list of conditions and the following
;;;     disclaimer in the documentation and/or other materials
;;;     provided with the distribution.
;;;
;;; THIS SOFTWARE IS PROVIDED BY THE AUTHOR 'AS IS' AND ANY EXPRESSED
;;; OR IMPLIED WARRANTIES, INCLUDING, BUT NOT LIMITED TO, THE IMPLIED
;;; WARRANTIES OF MERCHANTABILITY AND FITNESS FOR A PARTICULAR PURPOSE
;;; ARE DISCLAIMED.  IN NO EVENT SHALL THE AUTHOR BE LIABLE FOR ANY
;;; DIRECT, INDIRECT, INCIDENTAL, SPECIAL, EXEMPLARY, OR CONSEQUENTIAL
;;; DAMAGES (INCLUDING, BUT NOT LIMITED TO, PROCUREMENT OF SUBSTITUTE
;;; GOODS OR SERVICES; LOSS OF USE, DATA, OR PROFITS; OR BUSINESS
;;; INTERRUPTION) HOWEVER CAUSED AND ON ANY THEORY OF LIABILITY,
;;; WHETHER IN CONTRACT, STRICT LIABILITY, OR TORT (INCLUDING
;;; NEGLIGENCE OR OTHERWISE) ARISING IN ANY WAY OUT OF THE USE OF THIS
;;; SOFTWARE, EVEN IF ADVISED OF THE POSSIBILITY OF SUCH DAMAGE.
;;;
(in-package :CHAOS)
#|==============================================================================
                                 System: Chaos
                                 Module: comlib
                                File: process.lisp
==============================================================================|#
#-:chaos-debug
(declaim (optimize (speed 3) (safety 0) #-GCL (debug 0)))
#+:chaos-debug
(declaim (optimize (speed 1) (safety 3) #-GCL (debug 3)))

;;; *NOTE* GCL Specific

;;; ************************************
;;; SPAWNING PROCESS WITH TOW-WAY STREAM
;;; ************************************

;;;
;;; The following C codes are borrowed from GCL run_process.c
;;; with some minor bug fixes including enhancements by ishisone@sra.co.jp.
;;;

(Clines "
#undef PAGESIZE
#include <errno.h>      /* errno global, error codes for UNIX IO        */
#include <sys/types.h>  /* Data types definitions                       */
#include <sys/socket.h> /* Socket definitions with out this forget it   */
#include <netinet/in.h> /* Internet address definition AF_INET etc...   */
#include <signal.h>     /* UNIX Signal codes                            */
#include <sys/ioctl.h>  /* IO control standard UNIx fair                */
#include <sys/file.h>
#include <fcntl.h>      /* Function to set socket aync/interrupt        */
#include <sys/time.h>   /* Time for select time out                     */
#include <netdb.h>      /* Data Base interface for network files        */
/* patch by ishisone@sra.co.jp */
#include <sys/wait.h>   /* Wait system call options                     */
/* patch end */
#include <stdio.h>

static char *lisp_to_string(string)
object string;
{
        int     i, len;
        char    *sself;
        char    *cstr;

        len = string->st.st_fillp;

        cstr = (char *) malloc (len+1);
        sself = &(string->st.st_self[0]);
        for (i=0; i<len; i++)
        {
                cstr[i] = sself[i];
        }
        cstr[i] = 0;
        return (cstr);
}

/*
 * make 2 two-way streams
 */

static object
make_pipe()
{
  int sockets_in[2];
  int sockets_out[2];
  FILE *fp1, *fp2;
  int pid;
  object stream_in, stream_out, stream;

  if (socketpair(AF_UNIX, SOCK_STREAM, 0, sockets_in) < 0)
    FEerror(\"Failure to open socket stream pair\", 0);
  if (socketpair(AF_UNIX, SOCK_STREAM, 0, sockets_out) < 0)
    FEerror(\"Failure to open socket stream pair\", 0);
  fp1 = fdopen(sockets_in[0], \"r\");
  fp2 = fdopen(sockets_out[0], \"w\");

  stream_in = (object) alloc_object(t_stream);
  stream_in->sm.sm_mode = smm_input;
  stream_in->sm.sm_fp = fp1;
  stream_in->sm.sm_int0 = sockets_in[1];
  stream_in->sm.sm_int1 = 0;
  /* patch by sawada@sra.co.jp -- repairing printing problem */
  stream_in->sm.sm_object0 = sLstring_char;
  stream_in->sm.sm_object1 = Cnil;
  /* end patch */
  stream_out = (object) alloc_object(t_stream);
  stream_out->sm.sm_mode = smm_output;
  stream_out->sm.sm_fp = fp2;
  setup_stream_buffer(stream_in);
  setup_stream_buffer(stream_out);
  stream_out->sm.sm_int0 = sockets_out[1];
  stream_out->sm.sm_int1 = 0;
  /* patch by sawada@sra.co.jp -- ditto */
  stream_out->sm.sm_object0 = sLstring_char;
  stream_out->sm.sm_object1 = Cnil;
  /* patch end */
  stream = make_two_way_stream(stream_in, stream_out);
  return(stream);
}

/* the routines for spawning off a process with streams 
 *
 * Assumes that istream and ostream are both associated
 * with \"C\" type streams.
 */

static spawn_child(istream, ostream, pname, argv)
object istream;
object ostream;
char *pname;
char **argv;
{

  int fdin;
  int fdout;
  if (istream->sm.sm_fp == NULL || ostream->sm.sm_fp == NULL)
    FEerror(\"Cannot spawn process with given stream\", 0);
  fdin = istream->sm.sm_int0;
  fdout = ostream->sm.sm_int0;
  if (fork() == 0)
    { /* the child --- replace standard in and out with descriptors given */
      /* patch by ishisone@sra.co.jp */
      setsid();                         /* in order to get rid of job control */
      fclose(istream->sm.sm_fp);        /* close parent-side file desc. */
      fclose(ostream->sm.sm_fp);        /* ditto */
      /* end patch */
      close(0);
      dup(fdin);
      close(1);
      dup(fdout);
      if (execvp(pname, argv) == -1)
        {
          fprintf(stderr, \"\\n***** Error in process spawning *******\");
          fflush(stderr);
          exit(1);
        }
    }
    /* patch by ishisone@sra.co.jp */
    else
    { /* the parent */
       close(fdin);     /* close child-side file descriptor */
       close(fdout);    /* ditto */
     }
    /* end patch */
}
      
/*
#if defined(NeXT)
#  define WAITPID(pid, statusp, options) \
     wait3((union wait*)statusp, options, (struct rusage*)0)
#else
#  define WAITPID(pid, statusp, options) \
     waitpid(pid, statusp, options)
#endif
*/

/* patch by ishisone@sra.co.jp */
static reap_child()
{
/*
   int dummy;
   while (WAITPID(-1, &dummy, WNOHANG) > 0)
     ;
*/
}
/* end patch */

static run_child(file, arglist)
  object file;
  object arglist;
{
  char *filename = object_to_string(file);
  char *argv[100];
  object stream;
  int i;

  /* patch by ishisone@sra.co.jp */
  signal(SIGCHLD, reap_child);
  /* end patch */

  argv[0] = \"\";
  for(i = 1; arglist != Cnil; i++) {
     argv[i] = lisp_to_string(arglist->c.c_car);
     arglist = arglist->c.c_cdr;
  }
  argv[i] = (char *)0;

  stream = make_pipe();
  spawn_child(stream->sm.sm_object1,
              stream->sm.sm_object0,
              filename, argv);
  return(stream);

}
"
)

(defentry run-child (object object) (object run_child))

(defentry make-pipe () (object make_pipe))

;;;
;;; 
(defstruct process
  (name "" :type string :read-only t)
  (in-stream)
  (out-stream))

;;;
(defun run-process (program &optional args)
  (let ((stream (run-child program args)))
    (make-process :name program
                  :in-stream (si::fp-input-stream stream)
                  :out-stream (si::fp-output-stream stream))))

(defmacro with-write-to-process ((process) &body body)
  ` (let ((*standard-output* (process-out-stream ,process)))
      ,@body
      (finish-output)))

(defmacro with-read-from-process ((process) &body body)
  ` (let ((*standard-input* (process-in-stream ,process)))
      ,@body
      ))
