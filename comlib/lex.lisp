;;;-*- Mode:LISP; Package:CHAOS; Base:10; Syntax:Common-lisp -*-
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
(in-package :chaos)
#|==============================================================================
				  System:Chaos
				 Module:comlib
				 File: lex.lisp
==============================================================================|#
#-:chaos-debug
(declaim (optimize (speed 3) (safety 0) #-GCL (debug 0)))
#+:chaos-debug
(declaim (optimize (speed 1) (safety 3) #-GCL (debug 3)))

;;; ************
;;; TOKEN READER________________________________________________________________
;;; ************

;;; ** NOTES ON GENERAL ASSUMPTIONS AND LIMITATIONS.****************************
;;; <TODO>
;;;

;;;=============================================================================
;;; 		  *** CHAOS BUILTIN LEXICAL CATEGORIES ***
;;;=============================================================================

(eval-when (:execute :compile-toplevel :load-toplevel)
  (defvar *builtin-cats* (make-hash-table :test #'eq :size 50))
  (defmacro define-builtin-token (token-name id-value)
     ` (eval-when (:execute :compile-toplevel :load-toplevel)
         (defparameter ,token-name ,id-value)
         (setf (gethash ,id-value *builtin-cats*) t)))

  )

;;; Chaos BUILTIN LEXICAL CATEGORIES.
;;;-----------------------------------------------------------------------------

(defmacro declare-bi-token (sym)
  `(setf (get ,sym ':bi-token) t))

;;; The followings are builtin lexical units of Chaos system.

;;; Lisp expression.
(defparameter *lisp-escape-char* '|!|)
(defparameter .lisp-simple-sexpr. '%SLisp)
(defparameter .lisp-general-sexpr. '%GLisp)
;;; Chaos Value
(defparameter *chaos-escape-char* '|%|)
(defparameter .chaos-value-sexpr. '|%Chaos|)

;;; String&Character
(defparameter .String-token. '|String|)
;; (defparameter .Char-token. '|Character|)

(eval-when (:execute :load-toplevel)
  (declare-bi-token '%SLisp)
  (declare-bi-token '%GLisp)
  (declare-bi-token '|String|)
  (declare-bi-token '|%Chaos|)
  )

;;;=============================================================================
;;; LOW LEVEL READER
;;;=============================================================================

;;; Syntactic properties of characters:_________________________________________
;;; At the lowest level, each input character has a syntactic property which is 
;;; one of the followings:
;;;  - 'space  : means white space, i.e., normaly the chars chars except
;;;              cr/newline have this property.
;;;  - 'return : cr & newline.
;;;  ** 'white and 'return are always treated as token separators.
;;;  There are some chars which are treated as they stand, i.e., each of which
;;;  construct a token by itself. it is a resposibility of higher procs to treate
;;;  these chars in different ways. In such case, the value of the syntactic
;;;  property is set to a symbol other than 'space, 'return, or 'nil.
;;;  The property 'nil means that a sequnce of these char construct a token.
;;;  The global *reader-read-table* holds the above infos, `!init-read-table'
;;;  sets the property for each chars according to its arguments.
;;;
(declaim (type (integer 0 256) .reader-char-code-limit.))
(defparameter .reader-char-code-limit. 255) 
#-GCL (declaim (type simple-vector *reader-read-table*))
#+GCL (declaim (type vector *reader-read-table*))
(defvar *reader-read-table*)
(eval-when (:execute :load-toplevel)
  (setf *reader-read-table* (make-array (list .reader-char-code-limit.)
					:initial-element nil)))

(defmacro !set-syntax (ch val)
  `(setf (aref *reader-read-table* (the fixnum (char-code ,ch))) ,val))

(defun lex-show-delimiters (stream)
  (dotimes (x .reader-char-code-limit.)
    (let ((syntax (aref *reader-read-table* x)))
      (when syntax
	(format stream "~&~S : ~S" (code-char x) syntax)))))

;;; !INIT-READ-TABLE : List[Char] List[Char] List[Char] -> Void
;;; initialize Chaos read table.
;;;  space  : list of `space' characters
;;;  return : list of `return' characters
;;;  single : list of self terminatig characters
;;;
(defun !init-read-table (space return single)
  (declare (type list space return single)
	   (values t))
  #||
  (do ((i 0 (1+ i)))
      ((= i .reader-char-code-limit.))
    (declare (type (integer 0 256) i))
    (setf (aref *reader-read-table* i) nil))
  ||#
  (dolist (char space)
    (!set-syntax char 'space))
  (dolist (char return)
    (!set-syntax char 'return))
  (dolist (c-c single)
    (!set-syntax (car c-c) (cdr c-c))))

(defmacro reader-get-syntax (ch)
  `(if (< (char-code ,ch) .reader-char-code-limit.)
       (aref *reader-read-table* (the fixnum (char-code ,ch)))
     nil))

(defmacro reader-valid-char-code (n)
  (once-only (n)
    `(and (<= 0 ,n) (<= ,n .reader-char-code-limit.))))

;;; !SET-SINGLE-READER list-of-chars
;;; make a list of characters be single character symbols (self terminating)
;;; in the reader.
;;; returns list of original status. the return valu can be used for an argument 
;;; of `!set-reader' for recovering the modifications.
;;;
(defun !set-single-reader (l)
  (declare (type list l)
	   (values t))
  (mapcar #'(lambda (x)
	      (declare (type (or simple-string character) x))
	      (let ((chr (if (and (stringp x)
				  (= (length x) 1))
			     (char (the string x) 0)
			   (if (characterp x)
			       x
			     (with-output-chaos-error ('invalid-str)
			       (format t "delimiter must be a single character, but ~a is given" x))))))
		(prog1
		    (cons chr (reader-get-syntax chr))
		  ;; (print chr)
		  (!set-syntax chr (intern (string x))))))
	  l))

;;; !SET-READER list-of-chars
;;; modify a sequence of characters for syntax as given by associated values.
;;; useful for restoring the old properties of chars modified by !set-single-reader.
;;;
(defun !set-reader (l)
  (declare (type list l)
	   (values t))
  (mapc #'(lambda (x)
	    (declare (type list x))
            (let ((s (car x)))
	      (declare (type (or simple-string character) s))
	      (!set-syntax
	       (if (stringp s)
		   (char (the string s) 0)
		   s)
	       (cdr x))))
	l))

;;; !READ-IN
;;; read a token iff the last input is not processed yet,
;;; i.e. *reader-input* == *reader-void*.
;;; the token is set to *reader-input*.
;;;
;;; *reader-input* : token buffer.
;;;
(defvar *reader-input* nil)

;;; *reder-void* is the marker that indicates the buffered token is
;;; consumed, thus we should read a token.
;;;
(defparameter *reader-void* '(void))
(defvar *token-buf* nil)
(defvar *last-token* *reader-void*)

;;; The eof value.
(eval-when (:execute :compile-toplevel :load-toplevel)
  (defparameter *lex-eof* (cons nil nil))
  )

;;;
(defmacro !read-in ()
  ` (when (eq *reader-input* *reader-void*)
      (setq *reader-input* (read-sym))))

(defmacro reader-is-at-eof ()
  `(eq *lex-eof* *reader-input*))

(defmacro at-eof-or-control-d ()
  `(or (reader-is-at-eof)
       (equal *reader-input* control-d-string)))

;;; !READ-DISCARD
;;; discard the last input token.
;;;
(defmacro !read-discard ()
  `(progn ;; (clear-input)
	  ;; (setq *token-buf* nil)
	  (setq *reader-input* *reader-void*)))

;;; !READ-SYM
;;; read a token.
;;;
(defun !read-sym ()
  (cond ((eq *reader-input* *reader-void*) (read-sym))
	(t (prog1 *reader-input*
	     (!read-discard)))))

;;;
(defun test-lex (file)
  (!lex-read-init)
  (with-open-file (str file :direction :input)
    (let ((tok nil)
	  (*standard-input* str))
      (while-not (eq tok *lex-eof*)
         (setf tok (!read-sym))
	 (print tok)))))

;;; SIMPLE READER_______________________________________________________________
;;;

;;; READ-LINES (stream)
;;;
(defparameter newline-string (string #\newline))
(defparameter line-continue-char #\;)

(defparameter .read-line-eof. "")

(declaim (special *live-newline*))
(defvar *live-newline* nil)

(defmacro add-new-line (str)
  `(concatenate 'string ,str newline-string))

(defun read-lines (&optional (stream *standard-input*))
  (declare (type stream stream)
	   (values simple-string fixnum))
  (let (res
	line
	(ll 0)
	l-char 
	(l-total 0))
    (declare (type fixnum l-total ll))
    (loop (setq line (read-line stream nil .read-line-eof.))
      (when (eq line .read-line-eof.) (return))
      (when (<= (setq ll (length (the simple-string line))) 0)
	(return))
      (incf l-total ll)
      (decf ll)
      (setq l-char (char line ll))
      (if (char= line-continue-char (the character l-char))
	  (progn
	    (setq res (concatenate 'string res
				   (setq line (subseq (the simple-string line)
						      0 ll))
				   newline-string
				   ))
	    ;; (decf l-total)
	    (when (at-top-level)
	      (princ "> ")
	      (force-output)))
	(progn
	  (setq res (concatenate 'string
		      res
		      (if (char= #\. (the character l-char))
			  (progn
			    ;; (decf l-total)
			    (subseq line 0 ll))
			line)))
	  (return))))
    (if (eq line .read-line-eof.)
	(values *lex-eof* 0)
      (let ((str (if res
		     (if *live-newline*
			 (add-new-line res)
		       res)
		   "")))
	(values str (length str))))))

;;; the global .reader-ch. holds the last char read.
;;; if the character has a property other than 'nil, the property value is set,
;;; otherwise the character itself is set.
;;;
(defvar .reader-ch. 'space)

;;; the special .escape-char. holds a character which is used as escape
;;; character, i.e., the preceding char is treated as is.
;;;
(declaim (special .escape-char.))
(defvar .default-escape-char. #\\)

;;; 
#-CMU (defparameter control-d #\^D)
#+CMU (defparameter control-d #\)
(defparameter control-d-string "")
(defparameter input-escape #\esc)
(defparameter input-escape-string "")

(defmacro at-eof () `(eq *lex-eof* .reader-ch.))

(defmacro see-ctrl-d ()
  `(eq .reader-ch. control-d))

(defmacro see-input-escape ()
  `(eq .reader-ch. input-escape))
;; (defmacro see-input-escape ()
;;  `(eq .reader-ch. control-d))
  
(defun str-match? (x y)
  (declare (type t x)
	   (type (or symbol simple-string) y)
	   (values (or null t)))
  (or (eq x y)
      (and (stringp x)
	   (string= (the simple-string x)
		    (if (stringp y)
			(the simple-string y)
		      (string-downcase (string (the symbol y))))))))

(defun lex-string-match(x y)
  (declare (type t x)
	   (type (or atom list) y)
	   (values (or null t)))
  (if (atom y)
      (str-match? x y)
      (member x y :test #'str-match?)))

;;; READER-GET-CHAR : STREAM 
;;; reads a one character from stream, set .reader-ch. handling ESCAPE sequence.
;;;
(declaim (special .reader-escape.))
(defvar .reader-escape. nil)		; flags indicating we are now in `escaped'
					; status.

;; (defvar .read-buffer. nil)
;; (defvar .read-pos. 0)
(defvar .newline-count. 0)
(defvar *last-newline* nil)

(defparameter eof-char control-d)

(defun reader-get-char (stream)
  (declare (type stream stream)
	   (values t))
  (let ((inch (read-char stream nil *lex-eof*)))
    (cond ((eq inch *lex-eof*)
	   (setf .reader-ch. *lex-eof*))
	  #||
	  (.reader-escape.
	   (setf .reader-ch. inch))
	  ((char= .escape-char. inch)
	   (let ((.reader-escape. t))
	     (setf .reader-ch. 'space)
	     (reader-get-char stream)))
	  ||#
	  (t (unless *chaos-input-source*
	       ;; interactive session
	       (if (and (char= inch #\newline)
			*last-newline*)
		   (incf .newline-count.)
		 (if (char= inch #\newline)
		     (setq *last-newline* t)
		   (setf .newline-count. 0
			 *last-newline* nil)))
	       (when (> .newline-count. 2)
		 (!read-discard)
		 (clear-input)
		 (setq *last-newline* nil)
		 (setq .newline-count. 0)
		 (throw :aborting-read :aborting-read)))
	     ;;
	     (let ((val (reader-get-syntax inch)))
	       (setf .reader-ch. (if val val inch)))))))

; (defun reader-get-char (stream)
;   (declare (type stream stream)
; 	   (values t))
;   (let ((inch (read-char stream nil *lex-eof*)))
;     (cond ((eq inch *lex-eof*)
; 	   (setf .reader-ch. *lex-eof*))
; 	  #||
; 	  (.reader-escape.
; 	   (setf .reader-ch. inch))
; 	  ((char= .escape-char. inch)
; 	   (let ((.reader-escape. t))
; 	     (setf .reader-ch. 'space)
; 	     (reader-get-char stream)))
; 	  ||#
; 	  (t (let ((val (reader-get-syntax inch)))
; 	       (setf .reader-ch. (if val val inch)))))))

;;; READ-LEXICON : STREAM -> TOKEN
;;; read a lexicon.
;;;
;;; implementation limit: a lexicon must be of length less than or equal to 256.
;;;
(declaim (type simple-string .reader-buf.))
(defvar .reader-buf. (make-string 256))
(defparameter .chaos-simple-LISP-keyword. "#!")
(defparameter .chaos-general-LISP-keyword. "#!!")
(defparameter .chaos-value-keyword. "#%")

(defun read-lexicon (&optional (stream *standard-input*))
  (declare (type stream stream))
  (let ((p -1)
	res)
    (declare (type fixnum p)
	     (type (or symbol list simple-string) res))
    (setq res
	  (loop (cond ((member .reader-ch. '(#\Rubout #\Backspace))
		       (if (<= 0 p)
			   (decf p 1)))
		      ((characterp .reader-ch.)
		       (incf p)
		       (setf (aref .reader-buf. p) .reader-ch.))
		      (t (let ((c (string .reader-ch.)))
			   (setq .reader-ch. 'space)
			   (return c))))
		(reader-get-char stream)
		(when (at-eof)
		  (if (<= 0 p)
		      (progn (setq .reader-ch. 'space)
			     (return (subseq .reader-buf. 0 (1+ p))))
		      (return *lex-eof*)))
		(when (symbolp .reader-ch.)
		  (return (subseq .reader-buf. 0 (1+ p))))
		))
    ;;
    (lex-consider-token res)
    ))

(defun lex-consider-token (tok)
  (declare (type t tok))
  (if (equal .chaos-simple-LISP-keyword. tok)
      (progn (reader-suppress-ch tok) (list .lisp-simple-sexpr. (read)))
    (if (equal .chaos-general-lisp-keyword. tok)
	(progn (reader-suppress-ch tok) (list .lisp-general-sexpr. (read)))
      (if (equal .chaos-value-keyword. tok)
	  (progn (reader-suppress-ch tok) (list .chaos-value-sexpr. (read)))
	tok))))

(defun reader-suppress-ch (context &optional (stream *standard-input*))
  (declare (ignore context)
	   (type stream stream)
	   (values t))
  (unless (at-eof)
    (unless (memq .reader-ch. '(space return))
      (unread-char (if (characterp .reader-ch.)
		       .reader-ch.
		       (char (the simple-string (string .reader-ch.)) 0))
		   stream)
      (setq .reader-ch. 'space))))

(defun reader-unread (ch stream)
  (declare (type (or symbol character) ch)
	   (type stream stream)
	   (values t))
  (unless (memq ch '(space return))
    (unread-char (if (characterp ch)
		     ch
		     (char (the simple-string (string (the symbol ch))) 0))
		 stream)
    ch))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

;;; READ-SYM : STREAM -> TOKEN
;;; read characters considered to be constructs of a token, returns
;;; the token recognized.
;;; The followings are treated specially:
;;;  (...)   : read a parenthesized unit. 
;;;  "..."   : read as string constant.
;;;  'c      : read as character constant.
;;;
(defun unread-token (&rest ignore)
  (declare (ignore ignore)
	   (values t))
  (unless (eq *last-token* *reader-void*)
    (push *last-token* *token-buf*)
    (setq *last-token* *reader-void*)))

(defun read-sym (&optional (stream *standard-input*) (parse-list nil))
  (declare (type stream stream)
	   (type (or null t) parse-list)
	   (values t))
  (when *token-buf*
    (return-from read-sym (pop *token-buf*)))
  ;; skip white chars.
  (while (memq .reader-ch. (if *live-newline* '(space)
			     '(space return)))
    (reader-get-char stream))
  (cond (;; (or (at-eof) (see-ctrl-d))
	 (at-eof)
	 ;; (format t "~&we are at eof")
	 (setf .reader-ch. 'space)
	 (!read-discard)
	 *lex-eof*)
	((see-input-escape)
	 ;; user forces aborting reading process.
	 (setq .reader-ch. 'space)
	 (!read-discard)
	 (clear-input)
	 (throw :aborting-read :aborting-read))
	(t
	 (case .reader-ch.
	   (|(| (if parse-list
		    (setq *last-token* (lex-read-list stream))
		    (progn
		      (setq .reader-ch. 'space)
		      (setq *last-token* "("))))
	   (return
	     (setq .reader-ch. 'space)
	     (setq *last-token* (if *live-newline*
					  '(return)
					*reader-void*)))
	   (#\"				; string
	    (setq *last-token* (list (lex-read-string stream))))
	   (#\#				; #! or #!!
	    (reader-get-char stream)
	    (cond ((memq .reader-ch. '(space return))
		   (setq *last-token* '("#")))
		  ((eq .reader-ch. *lisp-escape-char*)
		   (setq *last-token* (lex-read-lisp-escape stream)))
		  ((eq .reader-ch. *chaos-escape-char*)
		   (setq *last-token* (lex-read-chaos-value stream)))
		  (t (reader-unread .reader-ch. stream)
		     (setq .reader-ch. #\#)
		     (let ((tok (read-lexicon stream)))
		       (if (equal tok *lex-eof*)
			   (progn (setq *last-token* *reader-void*)
				  *lex-eof*)
			   (setq *last-token* tok))))))
	   ;;
	   (otherwise
	    (if (symbolp .reader-ch.)
		(let ((str (string .reader-ch.)))
		  (setq .reader-ch. 'space)
		  (setq *last-token* (lex-consider-token str)))
		(let ((tok (read-lexicon stream)))
		  (if (eq tok *lex-eof*)
		      (progn (setq *last-token* *reader-void*)
			     *lex-eof*)
		      (setq *last-token* tok)))))))))

;;; builtin string reader
(defun lex-read-string (stream)
  (declare (type stream stream)
	   (values t))
  (reader-unread .reader-ch. stream)
  (let ((str (read stream nil *lex-eof*)))
    (if (eq str *lex-eof*)
	*lex-eof*
	(prog1 
	    (list .String-token. str)
	  (setf .reader-ch. 'space)))))

;; builtin lisp expression
(defun lex-read-lisp-escape (stream)
  (declare (type stream stream)
	   (values list))
  (let ((nx nil))
    (setq nx (reader-get-char stream))
    (while (memq .reader-ch. '(space return))
      (setq nx (reader-get-char stream)))
    (case nx
      ((*lisp-escape-char* *chaos-escape-char*)
       ;; #!!
       (let ((expr (read stream nil *lex-eof*)))
	 (setq .reader-ch. 'space)
	 (if (equal expr *lex-eof*)
	     (progn (setq *last-token* *reader-void*)
		    (setq .reader-ch. 'space)
		    *lex-eof*)
	   (list .lisp-general-sexpr. expr))))
      (otherwise
       ;; #!
       (let ((expr nil))
	 (setq .reader-ch. 'space)
	 (reader-unread nx stream)
	 (setq expr (read stream nil *lex-eof*))
	 (if (equal expr *lex-eof*)
	     (progn (setq *last-token* *reader-void*)
		    *lex-eof*)
	   (list .lisp-simple-sexpr. expr))))))
  )

(defun lex-read-chaos-value (stream)
  (declare (type stream stream)
	   (values list))
  (let ((expr (read stream nil *lex-eof*)))
    (setq .reader-ch. 'space)
    (if (equal expr *lex-eof*)
	(progn (setq *last-token* *reader-void*)
	       *lex-eof*)
      (list .chaos-value-sexpr. expr))))

;;; builtin character reader : obsolate
#||
(defun lex-read-character (stream)
  (let ((char (read-char stream nil *lex-eof*)))
    (if (eq char *lex-eof*)
	*lex-eof*
	(progn
	  (when (eql char #\\)		; escape char
	    (let ((echar (read-char stream nil *lex-eof*)))
	      (if (eq echar *lex-eof*)
		  (return-from lex-read-character *lex-eof*)
		  (setf char
			(case echar
			  (#\n #\Newline)
			  (#\r #\Return)
			  (#\t #\Tab)
			  (#\s #\Space)
			  (#\l #\LineFeed)
			  (#\p #\Page)
			  (otherwise echar))))))
	  (setf .reader-ch. 'space)
	  (list .Char-token. char)))))
||#

;;; read up to matching close parenthesis
;;;
(defun lex-read-list (&optional (stream *standard-input*))
  (declare (type stream stream))
  (reader-get-char stream)
  (lex-read-rest-of-list stream))

(defun lex-read-rest-of-list (&optional (stream *standard-input*))
  (declare (type stream stream)
	   (values list))
  (while (memq .reader-ch. '(space return))
    (reader-get-char stream))
  (if (at-eof)
      *lex-eof*
      (if (eq '|)| .reader-ch.)
	  (progn
	    (reader-get-char stream)
	    (list "(" ")"))
	  (let ((res (list "("))
		x)
	    (loop (setq x (lex-read stream))
		  (when (eq *lex-eof* x)
		    (return *lex-eof*))
		  (setq res (append res x))
		  ;; (wait-until-non-white stream)
		  (while (memq .reader-ch. '(space return))
		    (reader-get-char stream))
		  (when (eq '|)| .reader-ch.)
		    (reader-get-char stream)
		    (return (nconc res (list ")"))))
		  (when (at-eof)
		    (return *lex-eof*)))
	    ))))

;;; LEX-READ : STREAM -> List[Token]
;;; standard routine to get token from stream.
;;;
(defun bi-token? (tok)
  (declare (type t tok)
	   (values (or null t)))
  (and (consp tok)
       (let ((tm (car tok)))
	 (and (symbolp tm)
	      (get tm ':bi-token)))))

(defun lex-read (&optional (stream *standard-input*))
  (declare (type stream stream)
	   (values t))
  (let ((tok (read-sym stream t)))
    (if (eq *lex-eof* tok)
	*lex-eof*
	(cond ((atom tok)
	       (if tok
		   (list tok)
		   nil))
	      (t (if (bi-token? tok)
		     (list tok)
		     tok))))))

;;; returns t iff the characters in the string are all digit char.

(defmacro all-digit? (string start end)
  (once-only (string)
   ` (the (or null t)
       (do ((s (the fixnum ,start) (1+ s)))
	   ((>= s ,end) t)
	 (declare (type fixnum s end))
	 (if (not (digit-char-p (schar ,string s))) (return nil))))))
    
;;; BUFFERED-INPUT______________________________________________________________
;;; one token is bufferd.

;;; Input Buffering for general reader
;;;   the following routines create a single token buffer, which
;;;   allows look-ahead.
;;;

;;; !LEX-READ-INIT
;;; initialize read table, .escape-char., and .reader-ch..
;;;
(defparameter .default-space-chars.
  '(#\Space #\Tab #\Page #\Linefeed))

(defparameter .default-return-chars.
  '(#\Return #\Newline))

(defparameter .default-single-chars.
  `((#\( . |(|)
    (#\) . |)|)
    (#\, . |,|)
    (#\[ . |[|)
    (#\] . |]|)
    (#\{ . |{|)
    (#\} . |}|)
    (#\; . |;|)
    ;; (#\_ . |_|)
    ;; (#\% . "%")
    ;; (#\! . |!|)
    (,control-d . ,control-d)
    ))

(defun !force-single-reader (l)
  (declare (type list l)
	   (values t))
  (dolist (x l)
    (let* ((chr (if (and (stringp x)
			(= (length x) 1))
		   (char (the string x) 0)
		 (if (characterp x)
		     x
		   (with-output-chaos-error ('invalid-str)
		     (format t "delimiter must be a single character, but ~a is given" x)))))
	   (sym (intern (string x))))
      (format t "~&setting delimiters ~S : ~S" chr sym)
      (!set-syntax chr sym))))

(defun !unset-single-reader (l)
  (declare (type list l)
	   (values t))
  (dolist (x l)
    (let ((chr (if (and (stringp x)
			(= (length x) 1))
		   (char (the string x) 0)
		 (if (characterp x)
			       x
		   (with-output-chaos-error ('invalid-str)
		     (format t "Delimiter must be a single character, but ~a is given" x))))))
      (if (assoc chr .default-single-chars.)
	  (warn "Character '~A' is a hardwired self delimiting charcter, ignored."
		    chr)
	(progn
	  (format t "~&unsetting delimiters ~S" chr)
	  (!set-syntax chr nil))))))
;;;
;;;
;;;
(defun !lex-read-init (&key (space .default-space-chars.)
			    (return .default-return-chars.)
			    (single .default-single-chars.)
			    (escape .default-escape-char.))
  (!init-read-table space return single)
  (setq .escape-char. escape)
  (setq .reader-ch. 'space)
  (setq *reader-input* *reader-void*
	*last-token* *reader-void*
	*token-buf* nil))

;;; EOF
