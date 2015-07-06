;;;-*- Mode:Lisp; Syntax:Common-Lisp; Package:CHAOS -*-
;;;
;;; Copyright (c) 2000-2014, Toshimi Sawada. All rights reserved.
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
                              File: fsys.lisp
==============================================================================|#
#-:chaos-debug
(declaim (optimize (speed 3) (safety 0) #-GCL (debug 0)))
#+:chaos-debug
(declaim (optimize (speed 1) (safety 3) #-GCL (debug 3)))

#+:SBCL
(eval-when (:compile-toplevel :load-toplevel :execute)
  (require 'sb-posix))

;;; *****************
;;; FILE SYSTEM UTILS___________________________________________________________
;;; *****************

;;; LOAD-FILE : filename
;;; UNIX dependent.
(defun load-file (fname)
  (declare (type simple-string fname)
           (values t))
  (when (and (eql #\~ (char fname 0)) (eql #\/ (char fname 1)))
    (setq fname
          (concatenate 'string
            (namestring (user-homedir-pathname))
        (subseq fname 2))))
  (load fname))

#-GCL
(declaim (ftype (function ((or simple-string pathname)) simple-string)
                expand-file-name))

(defun expand-file-name (fname)
  (declare (type (or simple-string pathname) fname)
           (values simple-string))
  (if (pathnamep fname)
      (namestring fname)
    (progn
      (setq fname (namestring fname))
      (if (equal "~" fname)
          (namestring (user-homedir-pathname))
        (if (and (eql #\~ (char fname 0)) (eql #\/ (char fname 1)))
            (concatenate 'string
              (namestring (user-homedir-pathname)) (subseq fname 2))
          fname)))))

;;; DOFILE
;;;   Opens the specified file for input, reads successive lines 
;;;   from the file, setting the specified variable <var> to 
;;;   each line. When end of file is reached, the value of <return-form>
;;;   is returned.

(defmacro dofile ((var filename &optional return-form) &body body)
  (let ((eof (gensym "EOF"))
        (stream (gensym "STREAM")))
    `(with-open-file (,stream ,filename :direction :input)
       (do ((,var (read-line ,stream nil ,eof)
                  (read-line ,stream nil ,eof)))
           ((eq ,var ,eof)
            ,return-form)
         ,@body))))

;;;
;;;
;;;

(defun is-directory? (path)
  (declare (type (or pathname simple-string) path))
  (let ((dpath (expand-file-name path)))
    #+(or GCL CMU :openmcl)
    (probe-file (concatenate 'string dpath "/"))
    #+:SBCL
    (let ((directory-delimiter "/")  ; sbcl uses / on all platforms!
          (p (probe-file dpath)))
      (if p
          (and (string-equal (subseq (namestring p)
                                     (1- (length (namestring p))))
                             directory-delimiter)
               p)
        nil))
    #+:Allegro
    (if (excl:file-directory-p dpath)
        (pathname (concatenate 'string dpath "/"))
      nil)
    #+(and :CCL (not :openmcl)) (if (directoryp dpath) dpath nil)
    #+:CLISP
    (let ((p (concatenate 'string dpath "/")))
      (if (directory p) ;; (ext:probe-directory path)
          p
        nil))))

(defun is-simple-file-name? (path)
  (declare (type (or simple-string pathname) path)
           (values (or null t)))
  (if (pathnamep path)
      (null (pathname-directory path))
    (if (stringp path)
        (let ((dir (pathname-directory (pathname path))))
          (if (or (null dir)
                  (equal '(:relative) dir))
              t
            nil))
      (error "is-simple-file-name? : given non string arg ~a" path))))

(defun supply-suffixes (path suffixes)
  (declare (type (or simple-string pathname) path)
           (type list suffixes)
           (values list))
  (mapcar #'pathname
          (mapcar #'(lambda (x) (concatenate 'string
                                  (namestring path)
                                  (namestring x)))
                  suffixes)))

(defun chaos-probe-file (file load-path suffixes)
  (declare (type (or simple-string pathname) file)
           (type (or simple-string list) load-path)
           (type list suffixes))
  (when (and (pathnamep file) (not (is-directory? file)))
    (return-from chaos-probe-file (probe-file file)))
  ;;
  (setq file (expand-file-name file))
  (when (atom suffixes)
    (setq suffixes (list suffixes)))
  (when (and load-path (atom load-path))
    (setq load-path (list load-path)))
  ;;
  (cond ((is-simple-file-name? file)
         (let ((file-path (chaos-get-relative-path*
                           (concatenate 'string "./" file)))
               (res nil))
           ;;
           (setq res (probe-file file-path))
           (when (and res (is-directory? res))
             (setq res nil))
           (unless res
             (dolist (fx (supply-suffixes file-path suffixes))
               (when (and (probe-file fx) (not (is-directory? fx)))
                 (setq res fx)
                 (return)))
             ;; search through load paths
             (unless res
               (dolist (lpath load-path)
                 (let ((libdir (is-directory? lpath)))
                   (declare (type (or null string pathname) libdir))
                   (when libdir
                     (unless (pathnamep libdir) (setq libdir (pathname libdir)))
                     (let ((f (make-pathname
                               :host (pathname-host libdir)
                               :device (pathname-device libdir)
                               :directory
                               #+:CLISP libdir
                               ;; #+:Allegro (namestring libdir)
                               #-:CLISP (pathname-directory libdir)
                               :name (namestring file))))
                       (if (and (probe-file f) (not (is-directory? f)))
                           (progn (setq res f) (return))
                         (let ((x (supply-suffixes f suffixes)))
                           (dolist (fx x)
                             (when (and (probe-file fx) (not (is-directory? fx)))
                               (setq res fx)
                               (return)))))))))))
           res))
        (t (let ((file-path (chaos-get-relative-path* file)))
             (if (and (probe-file file-path) (not (is-directory? file-path)))
                 file-path
               (dolist (fx (supply-suffixes file-path suffixes))
                 (when (and (probe-file fx) (not (is-directory? fx)))
                   (return-from chaos-probe-file fx))))))))

(defun bare-chaos-pwd ()
  #+GCL (probe-file ".")
  #+EXCL (excl::current-directory)
  #+CMU (ext:default-directory)
  #+:SBCL (car (directory "./"))
  #+:CCL (mac-default-directory)
  #+:CLISP (car (lisp:directory "./")))

(defun chaos-pwd ()
  (declare (values simple-string))
  (namestring (bare-chaos-pwd)))

(defun chaos-relative-pathname? (f-name)
  (let ((fdp (pathname-directory (pathname f-name))))
    (or (null fdp)
        (and fdp                        ; not simple file name.
             (not (eq (car (pathname-directory (pathname f-name)))
                      :root))))))

(defun chaos-get-relative-path (f-name)
  (setq f-name (expand-file-name f-name))
  (chaos-get-relative-path* f-name))

; #+:SBCL
; (defun chaos-get-directory (file-path)
;   (let* ((ns (namestring file-path))
;        (dpos (position #\/ ns :from-end t))
;        (dir nil))
;     (unless dpos
;       (with-output-chaos-error ('internal-error)
;       (format t ":get-relative-path: could not find proper directory path, ~a" file-path)))
;     (subseq ns 0 (1+ dpos))))

#+(or :Allegro :SBCL)
(defun chaos-get-directory (file-path)
  (unless (pathnamep file-path)
    (setq file-path (pathname file-path)))
  (let ((dir-path (make-pathname :host (pathname-host file-path)
                                 :device (pathname-device file-path)
                                 :directory (pathname-directory file-path))))
    ;;(namestring dir-path)
    dir-path))

(defun chaos-get-relative-path* (f-name)
  (if (null *chaos-input-source*)
      (pathname f-name)
    (if (chaos-relative-pathname? f-name)
        (let ((f-path nil))
          (unwind-protect
              (let ((host (pathname-host (pathname f-name)))
                    (device (pathname-device (pathname f-name)))
                    (fd (pathname-directory (pathname f-name)))
                    (f (file-namestring (pathname f-name))))
                ;; #-GCL (declare (ignore fd))
                ;; (chaos-pushd (directory-namestring *chaos-input-source*))
                (chaos-pushd (chaos-get-directory *chaos-input-source*))
                #+GCL
                (setq f-path (truename (make-pathname :directory fd :name f)))
                #+:CLISP
                (setq f-path (make-pathname
                              :host host
                              :device device
                              :directory fd ;; (pathname fd)
                              :name f))
                #-(or GCL :CLISP)
                (progn
                  (setq f-path (make-pathname
                                :host host
                                :device device
                                :directory fd
                                :name f))))
            (chaos-popd))
          f-path)
      ;; absolute path or simple filename.
      (pathname f-name))))

#+(or (and CCL (not :openmcl)) :microsoft)
(defun chaos-ls (&optional (dir "**"))
  (pprint (mapcar #'(lambda (x)
                      (file-namestring x))
                  (directory dir))))

#+(or GCL LUCID (and EXCL (not :microsoft)) CLISP :openmcl SBCL)
(defun chaos-ls (&optional dir)
  (let ((comm '("ls"))
        (args (if (and dir (atom dir))
                  (list dir)
                dir)))
    (setq comm (reduce #'(lambda (x y) (concatenate 'string x " " y))
                       (append comm args)))
    #+GCL (system comm)
    #+EXCL (excl:shell comm)
    #+SBCL (apply #'sb-ext:run-program
                  #+win32 "CMD" #-win32 "/bin/sh"
                  #+win32 (list "/c" "dir") #-win32 (list  "-c" comm)
                  :input nil :output *terminal-io*
                  #+win32 '(:search t) #-win32 nil)
    #+LUCID (lucid::%execute-system-command comm)
    #+CLISP (ext::shell comm)))

#+(or CMU :openmcl)
(defun chaos-ls (&optional args)
  (if (and args (atom args))
      #+CMU (ext::run-program "ls" (list args) :output t)
      #+:openmcl (ccl::run-program "ls" (list args) :output t)
      #+CMU
      (if args
          (ext::run-program "ls" args :output t)
        (ext::run-program "ls" nil :output t)
        )
      #+:penmcl
      (if args
          (ccl::run-program "ls" args :output t)
        (ccl::run-program "ls" nil :output t))))

(defvar *chaos-directory-stack* nil)

(defun chaos-print-directory-stack (&optional (stream *standard-output*))
  (format stream "~%~a" *chaos-directory-stack*))

(defun fsys-parse-number (tok)
  (declare (type (or simple-string pathname) tok))
  (if (stringp tok)
      (let ((minusp nil))
        (if (char= (char tok 0) #\-)
            (setq minusp t)
          (unless (char= (char tok 0) #\+)
            (return-from fsys-parse-number
              (values tok nil))))
        (let ((num (read-from-string tok)))
          (if (numberp num)
              (values num minusp)
            (values tok nil))))
    (values tok nil)))

(defun chaos-pushd (arg &optional (always-return nil))
  (let ((path arg))
    (cond (arg
           (multiple-value-bind (num minusp)
               (fsys-parse-number arg)
             (cond ((numberp num)
                    (let ((new-stack (rotate-list *chaos-directory-stack*
                                                  num minusp)))
                      (if new-stack
                          (setq *chaos-directory-stack* new-stack)
                        (with-output-chaos-warning ()
                          (format t "directory stack is not so deep.")
                          (return-from chaos-pushd nil)))
                      (setq path (car *chaos-directory-stack*))))
                   (t (push :dymmy *chaos-directory-stack*)))
             (if (chaos-cd path always-return)
                 t
               (progn
                 (pop *chaos-directory-stack*)
                 nil))))
          (t (if (<= (length *chaos-directory-stack*) 1)
                 (with-output-chaos-warning ()
                   (format t "No other directory.")
                   (return-from chaos-pushd nil))
               (chaos-pushd "+1"))))))

(defun chaos-popd (&optional num)
  (declare (ignore num))
  (if (cdr *chaos-directory-stack*)
      (let ((xd nil))
        (pop *chaos-directory-stack*)
        (setq xd (car *chaos-directory-stack*))
        (chaos-cd xd))
    ;; do nothig
    #||
    (with-output-chaos-warning ()
      (format t "directory stack is empty!"))
    ||#
    ))

(defun chaos-cd (path &optional (always-return nil))
  (let ((directory-path nil)
        (ng nil))
    (unless path
      (setq path (user-homedir-pathname)))
    #+GCL (let ((si::*break-enable* nil))
            (if (setq directory-path (is-directory? path))
                (system:chdir directory-path)
              (setq ng t)))
    #+CMU (if (setq directory-path (is-directory? path))
              (progn (lisp::%set-default-directory directory-path))
            (setq ng t))
    #+EXCL (if (setq directory-path (is-directory? path))
               (excl::chdir directory-path)
             (setq ng t))
    #+:openmcl (if (setq directory-path (is-directory? path))
                   (progn (ccl::%chdir (namestring directory-path)))
                 (setq ng t))
    #+SBCL
    (if (setq directory-path (is-directory? path))
        (progn
          (setq *default-pathname-defaults* directory-path)
          (sb-posix:chdir directory-path))
      (setq ng t))
    #+(and :CCL (not :openmcl))
    (if (setq directory-path (is-directory? path))
        (set-mac-default-directory directory-path)
      (setq ng t))
    #+:CLISP (if (setq directory-path (is-directory? path))
                 (setq *default-pathname-defaults*
                   (ext:cd directory-path))
               (setq ng t))
    ;;
    (cond (ng (with-output-chaos-warning ()
                (format t "directory \"~a\" not found." path))
              (if always-return
                  (return-from chaos-cd nil)
                (chaos-error 'no-such-directory)))
          (t (let ((cwd (chaos-pwd)))
               #||
               #-CLISP
               (setq *default-pathname-defaults* cwd)
               #+CLISP
               ||#
               (setq *default-pathname-defaults* (pathname cwd))
               (if *chaos-directory-stack*
                   (setf (car *chaos-directory-stack*)
                     *default-pathname-defaults*)
                 (setf *chaos-directory-stack*
                   (list *default-pathname-defaults*))))))
    *default-pathname-defaults*))

(defparameter *chaos-binary-magic* ";CHAOS_BINS_____")

(defun chaos-binary-file? (file)
  (with-open-file (*standard-input* file :direction :input)
    (let ((magic (read-line)))
      (equal magic *chaos-binary-magic*))))

(defparameter *chaos-bin-suffix* '(".bin"))

(defun chaos-input-file (&key file      ; input file name
                              proc      ; procedure
                              load-path ; list of pathnames
                              (suffix '(".cafe" ".mod"))
                              args      ; args to be passed to proc
                              (errorp t) ; 
                              )
  (let ((fname (chaos-probe-file file load-path suffix))
        (bin-fname (chaos-probe-file file load-path *chaos-bin-suffix*)))
    (when (and fname (is-directory? fname))
      (with-output-chaos-error ('invalid-file)
        (format t "~a is not a proper file." (namestring file)))
      (return-from chaos-input-file nil))
    (unless (or fname bin-fname)
      (if errorp
          (with-output-chaos-error ('no-such-file)
            (format t "no such file: ~a" (namestring file)))
        (return-from chaos-input-file nil)
        ))
    (when (and bin-fname fname (>= (file-write-date bin-fname)
                                   (file-write-date fname)))
      (setq fname bin-fname))
    (unless fname
      (setq fname bin-fname))

    (when (equal *chaos-input-source* fname)
      (return-from chaos-input-file t))

    (let ((*chaos-input-source* fname)
          (*chaos-input-level* (1+ *chaos-input-level*)))
      (if (chaos-binary-file? fname)
          (progn (load fname) fname)
        (with-open-file (*standard-input* fname :direction :input)
          (when (< *chaos-input-nesting-limit* *chaos-input-level*)
            (with-output-chaos-warning ()
              (format t "input nesting is ~d~%" *chaos-input-level*)
              (print-next)
              (princ "probable input loop (can increase *chaos-input-nesting-limit*)")
              ))
          (apply proc args)
          fname
          )))))
;;;
(defun set-search-path (paths)
  (when (consp paths)
    (setq paths (car paths)))
  (let ((path nil))
    (dolist (p (parse-with-delimiter paths #\:))
      (push p path))
    (setq *chaos-libpath* (nreverse path))))

(defun set-search-path-plus (paths)
  (when (consp paths) (setq paths (car paths)))
  (let ((path nil))
    (dolist (p (parse-with-delimiter paths #\:))
      (push p path))
    (setq *chaos-libpath*
          (append (nreverse path) *chaos-libpath*))))

(defun set-search-path-minus (paths)
  (when (consp paths) (setq paths (car paths)))
  (let ((path nil))
    (dolist (p (parse-with-delimiter paths #\:))
      (push p path))
    (dolist (p path)
      (if (not (member p *chaos-libpath* :test #'equal))
          (with-output-chaos-warning ()
            (format t "The path ~s does not in 'libpath'." p))
        (setq *chaos-libpath* (remove p *chaos-libpath* :test #'equal))))
    *chaos-libpath*))

(defun pr-search-path (&optional (stream *standard-output*))
  (format stream "libpath = ~{~a~^:~}" *chaos-libpath*))

;;;
;;; INITIALIZATION
;;;
(defun chaos-initialize-fsys ()
  ;; any other?
  (setq *chaos-directory-stack* nil)
  (push (setq *default-pathname-defaults* (bare-chaos-pwd))
        *chaos-directory-stack*)
  ;; very old stuff
  #+(and :ccl (not :openmcl))
  (progn (setq *default-pathname-defaults*
           (full-pathname (mac-default-directory)))
         (set-mac-default-directory *default-pathname-defaults*)))

;;; EOF
