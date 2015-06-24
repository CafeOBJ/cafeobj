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
                               File: reader.lisp
==============================================================================|#
#-:chaos-debug
(declaim (optimize (speed 3) (safety 0) #-GCL (debug 0)))
#+:chaos-debug
(declaim (optimize (speed 1) (safety 3) #-GCL (debug 3)))

;;;                       SCHEMA BASED Genral Reader.
;;;
;;; BASED ON OBJ3 READER ROUTINES.
;;; ;;;; Copyright 1988,1991 SRI International.
;;; 

;;; SCHEMA
;;;=============================================================================
;;; Schemas match patterns
;;; choices must be determined by first symbol of context
;;;   e.g. if an optional element doesn't occur what occurs first
;;;     must be an explicit symbol in the schema
;;;
;;;--- BUILT-IN PATTERNS -------------------------------------------------------
;;; To parse the OBJ3 syntax more easier, these definitions are just the same
;;; as of OBJ3 schema.
;;;
;;; (:optional PAT)  - optional occurrence of pattern
;;; (:if-present PAT)  - optional occurrence of pattern
;;; *NOTE*
;;;   :optional - omit if next token matches following context
;;;   :if-present - assume if first matches
;;; (:one-of PAT1 PAT2 ...) - one of patterns determined by first of patterns
;;; (:one-of-default PAT1 PAT2 ...) ... with a default to PAT1
;;; (:seq-of PAT) - some number of repetitions of PAT
;;; (:many-of PAT1 PAT2 ...) - roughly (:seq-of (:one-of PAT1 ...))
;;; :symbol - a symbol
;;; :symbols - (:seq-of :symbol)
;;; :int - an integer
;;; :term - sequence of tokens up to terminator which follows
;;; :sort - a sort name (possibly qualified)
;;; :sorts - (:seq-of :sort)
;;; :comment - string of characters to end of current line
;;; :commentlong - variation of above with provision for long comments
;;; (:+ a b c) - any of several symbols
;;; (:! SCHEMA-NAME) - match the named schema
;;; (:call LISP-EXPR) - escape to Lisp
;;; (:rdr ("char1" "char2"...) PAT) - make characters be single-char and
;;;   then match pattern, returning status of characters to previous when done
;;; :modexp - read a term with balanced (/) [/] view/endv
;;;   particular tricky case: view A to B[view C to D is ... endv] { ... }
;;; :chaos-item - read a (possibly parenthesized) item
;;; otherwise: symbol - matches symbol if it is not defined as the schema name.
;;; (:pred PREDICATE) - matches a token satisfying predicate
;;; :append PAT - analogous to ,@; incorporate structure from PAT
;;;               into result "removing one set of parentheses"
;;; :upto - specify ending context for repeated form
;;; :args - for command arguments. read rest of line till \newline.
;;;
;;;--- DEFINING NEW SCHEMA & Its Reader ....


(defvar *reader-special-schema-patterns* nil)

;;; READER schema-pattern-name schemas
;;; read input from *standard-input*, parse according to schemas
;;;
(defun reader (name schms)
  (declare (type symbol name)
           (type list schms)
           (values t))
  (let ((*reader-schema-env* schms))
    (!lex-read-init)
    (read-named name *reader-void* nil)
  ))

;;; 
;;; ERROR HANDLERS
;;;

(defun abort-general-reader (msg)
  (with-output-chaos-error ('reader-error)
    (princ msg)
    (when *chaos-input-source*
      (print-next)
      (princ "file: ")
      (princ (namestring *chaos-input-source*)))
    (when (and *reader-current-schema*
               (general-read-is-simple-schema *reader-current-schema*))
      (print-next)
      (princ "expecting: ")
      (let ((*print-indent-contin* t))
        ;; (break)
        ;; (general-read-print-schema *reader-current-schema*)
        (general-read-display-schema *reader-current-schema* :short)))
    (when *reader-starting-position*
      (print-next)
      (princ "starting character position was: ")
      (princ *reader-starting-position*))))

(defun general-read-eof-error ()
  (declare (values t))
  (abort-general-reader "Unexpected EOF."))

(defun general-read-abort ()
  (declare (values t))
  (abort-general-reader "Cancel reading input..."))

;;; STRING-MATCH string1 string2
;;; basic string matching function.
;;;
(defun string-match (x y)
  (declare (values (or null t)))
  (cond ((stringp x)
         (string= (the simple-string x)
                  (if (stringp y)
                      (the simple-string y)
                    (the simple-string
                      (string-downcase (string y))))))
        ((characterp x)
         (eql (the character x) (the character y)))
        (t (eq x y))))

;;; GENERAL-READ-STRING-MATCHES : token pattern -> Bool
;;; used to match tokens against "patterns" which should be
;;;   either a symbol, string, or of one of the forms
;;;   (:+ a b c ...) or (:pred PRED)
;;;
(defun general-read-string-matches (x y)
  (declare (values (or null t)))
  (and (atom x)
       (if (atom y) (string-match x y)
           (or (and (eq ':pred (car y)) (funcall (cadr y) x))
               (if (eq ':+ (car y)) 
                   (member x (cdr y) :test #'string-match)
                   (member x y :test #'string-match))))))

;;; GENERAL-READ-NUMBERP token -> Bool 
;;; is a token an integer?
;;;
(defun general-read-numberp (str)
  (declare (type simple-string str)
           (values (or null t)))
  (let ((p 0)
        (len (length str)))
    (declare (type fixnum p len))
    (when (member (char str p) '(#\+ #\-))
      (incf p)
      (when (= 1 len) (return-from general-read-numberp nil)))
    (loop
        (when (= len p) (return t))
        (when (not (digit-char-p (char str p))) (return nil))
      (incf p)
      )))

;;; GENERAL-READ
;;; the workhorse general read routine
;;;   it dispatches to routines to handle the various cases
;;; op general-read : {*standard-input*} schema context ->
;;;                         {*standard-input*} parse-tree

(defun general-read (schema context &optional (allow-other nil))
  (declare (type list schema context)
           (type (or null t) allow-other)
           (values t))
  ;;
  (let ((*reader-current-schema* schema)
        (*reader-current-context* context)
        (*reader-starting-position* 
         (if (at-top-level) nil (file-position *standard-input*)))
        (result nil))
    (setq result
      (catch :aborting-read
        (cond ((null schema) nil)
              (t (let ((elt (car schema))
                       (rest (cdr schema)))
                   (let ((restcontext (if rest rest context)))
                     (cond
                      ((symbolp elt)
                       (case elt
                         (:unread (read-continue (unread-token)
                                                 rest context))
                         (:optional (read-optional rest context))
                         (:if-present (read-if-present rest context))
                         (:one-of (read-one-of rest context))
                         (:one-of-default (read-one-of-default rest context))
                         (:many-of      ;like one-of but with repetitions
                          (read-many-of rest context))
                         (:seq-of (read-seq-of rest context))
                         (:symbol (read-continue (!read-sym) rest context))
                         (:symbols (read-continue (read-seq-of '(:symbol)
                                                               restcontext)
                                                  rest context))
                         (:int (let ((val (!read-sym)))
                                 (cond
                                  ((general-read-numberp val)
                                   (read-continue val rest context))
                                  (t (with-output-chaos-error ('reader-error)
                                       (princ "was expecting an integer not ")
                                       (princ val)
                                       (print-next)
                                       (general-read-show-context)
                                       (clear-input)
                                       )))))
                         (:top-term (read-continue (read-term-at-top restcontext)
                                                   rest context))
                         (:term (read-continue (read-term restcontext)
                                               rest context))
                         ;; (:term-to (read-continue (read-term-to restcontext)
                         ;;                          rest context))
                         (:top-opname (read-continue (read-opname-at-top restcontext)
                                                     rest context))
                         (:opname (read-continue (read-opname restcontext)
                                                 rest context))
                         (:sort (read-continue (read-sort restcontext)
                                               rest context))
                         (:sorts (read-continue (read-sorts restcontext)
                                                rest context))
                         (:chars (read-continue (read-chars restcontext)
                                                rest context))
                         (:optattr (read-continue (read-opattr restcontext)
                                                  rest context))
                         (:comment (read-continue (read-comment-line) rest context))
                         (:commentlong
                          (read-continue (general-read-commentlong) rest context))
                         (:+ (read-any-one rest))
                         (:!            ; use named description
                          (read-named (car rest) context))
                         (:call (eval (car rest)))
                         (:append
                          (let* ((rr (cdr rest))
                                 (rc (if rr rr context)))
                            (read-continue-append
                             (general-read (car rest) rc) rr context)))
                         (:rdr
                          (let ((cur (!set-single-reader (car rest))))
                            (prog1 (general-read (cdr rest) context)
                              (!set-reader cur))))
                         (:modexp
                          (read-continue
                           (read-module-exp (car restcontext)) rest context))
                         (:super
                          (read-continue
                           (read-super-exp (car restcontext)) rest context))
                         (:chaos-item 
                          (!read-discard)
                          (let ((val (lex-read)))
                            (let ((a (if (null (cdr val)) (car val) val)))
                              (read-continue a rest context))))
                         (:args
                          (read-args rest context))
                         (otherwise
                          (if allow-other
                              ;; we read input as a seq-of term
                              (general-read '(:seq-of :term) '(void))
                            (progn
                              (!read-in)
                              (cond
                               ((string-match *reader-input* elt)
                                (let ((inp *reader-input*))
                                  (!read-discard)
                                  (read-continue inp rest context)))
                               (t (with-output-chaos-error ('reader-error)
                                    (princ "was expecting the symbol ")
                                    (princ "`")
                                    (princ elt)
                                    (if (or (equal *reader-input* *lex-eof*)
                                            (equal *reader-input* control-d-string))
                                        (format t "', premature end of input.")
                                      (format t "' not `~a'." *reader-input*))
                                    (print-next)
                                    (general-read-show-context)
                                    (clear-input)
                                    ))))))
                         ))
                      ((member (car elt) '(:! :rdr))
                       (let ((val (general-read elt restcontext)))
                         (cond ((eq *reader-void* val)
                                (general-read rest context))
                               (t (append val
                                          (general-read rest context))))))
                      ((eq :upto (car elt))
                       (append (general-read (cddr elt) (list (cadr elt)))
                               (general-read rest context)))
                      (t
                       (read-continue (general-read elt restcontext) rest context)
                       ))))))
        ))
    (if (eq :aborting-read result)
        (general-read-abort)
      result)
    ))

;;; PATTERN HANDLERS
;;; 

;;; READ-NAMED name context
;;;
(defun read-named (name context &optional allow-other)
  (declare (type symbol name)
           (type list context)
           (type (or null t) allow-other))
  (let ((val (assoc name *reader-schema-env* :test #'eq)))
    (cond (val (general-read (cadr val) context allow-other))
          (t (error "Undefined name in general reader ~a" name)))))

;;; READ-OPTIONAL
;;;
(defun read-optional (s c)
  (!read-in)
  (when (at-eof-or-control-d)
    (general-read-eof-error))
  (cond  ((general-read-string-matches *reader-input* (car c))
          *reader-void*)
         (t (general-read s c)))
  )

;;; READ-IF-PRESENT
;;;
(defun read-if-present (s c)
  (declare (type list s c)
           (values t))
  (!read-in)
  (when (at-eof-or-control-d)
    (general-read-eof-error))
  (cond ((general-read-string-matches *reader-input* (car s))
         (general-read s c))
        (t *reader-void*)))

;;; READ-ONE-OF
;;;
(defun read-one-of (s c)
  (declare (type list s c)
           (values t))
  (let ((inp (!read-sym)))
    (when (and c (at-eof-or-control-d))
      (general-read-eof-error))
    (let ((val (assoc inp s :test #'general-read-string-matches)))
      (cond (val (cons inp (general-read (cdr val) c)))
            ((and (consp inp)
                  (eq (caar inp) '|String|))
             (read-one-of s c))
            ((and (eq *lex-eof* inp)
                  (assoc 'eof s))
             (cons 'eof (general-read (cdr (assoc 'eof s)) c)))
            ((eq *lex-eof* inp) (general-read-eof-error))
            (*allow-general-term-input*
             (unread-token)
             (read-term '(|.|)))
            (t (let ((top-level (assoc 'eof s)))
                 (when (equal inp ".")
                   (chaos-error 'reader-error))
                 (with-output-chaos-error ('reader-error)
                   (princ "expecting one of followings:")
                   (print-next)
                   (let ((*print-indent-contin* t))
                     (general-read-print-schema (mapcar #'car s) :short))
                   (print-next)
                   (princ "* NOT: ")
                   (princ inp)
                   (general-read-show-context)
                   (when top-level
                     (setq *chaos-print-errors* nil))
                   (clear-input)
                   )))
            ))))


;;; READ-ONE-OF-DEFAULT
;;; first alternative is a default
;;;
(defun read-one-of-default (s c)
  (declare (type list s c)
           (values t))
  (!read-in)
  (let ((val (assoc *reader-input* (cdr s)
                    :test #'general-read-string-matches)))
    (cond (val (let ((inp *reader-input*))
                 (!read-discard)
                 (cons inp (general-read (cdr val) c))))
          ((and (reader-is-at-eof) (assoc 'eof s))
           (cons 'eof (general-read (cdr (assoc 'eof s)) c)))
          ((reader-is-at-eof)           ; !!!
           (general-read-eof-error))
          (t (general-read (car s) c)))))

;;; READ-MANY-OF
;;;
(defun read-many-of (s c)
  (declare (type list s c)
           (values t))
  (let ((res nil) (close (car c)))
    (loop (!read-in)
          (when (at-eof-or-control-d)
            (general-read-eof-error))
          (when (general-read-string-matches *reader-input* close)
            (return (if (null res)
                        *reader-void*
                        (nreverse res))))
          (if (and (consp *reader-input*)
                   (eq (caar *reader-input*) '|String|))
              (setq *reader-input* *reader-void*)
              (setq res (cons (read-one-of s c) res))))))

;;; READ-SEQ-OF
;;;
(defun read-seq-of (s c)
  (declare (type list s c)
           (values t))
  (cond ((equal '(:term) s) (read-seq-of-term c))
        ((equal '(:opname) s) (read-seq-of-opname c))
        ((equal '(:top-term) s) (read-seq-of-term-at-top c))
        ((equal '(:top-opname) s) (read-seq-of-opname-at-top c))
        (t (let ((res nil) (close (car c)))
             (loop
              (!read-in)
              (when (at-eof-or-control-d)
                (general-read-eof-error))
              (when (general-read-string-matches *reader-input* close)
                (return (if (null res) *reader-void* res)))
              (setq res (append res (general-read s c)))
              )))))

;;; READ-ANY-ONE
;;;
(defun read-any-one (s)
  (declare (type list s)
           (values t))
  (!read-in)
  (cond ((member *reader-input* s :test #'string-match)
         (!read-sym))
        ((at-eof-or-control-d) (general-read-eof-error))
        (t (with-output-chaos-error ('reader-error)
             (princ "expecting one of")
             (print-next)
             (let ((*print-indent-contin* t))
               (general-read-print-schema s :short))
             (print-next)
             (format t "NOT ")
             (princ *reader-input*)
             (general-read-show-context)
             (clear-input)
             ))))

;;; READ-CONTINUE : {*standard-input*} value schema context ->
;;;   {*standard-input*} parse-tree
;;; continues the matching process
;;; the value is returned as the first component of the resulting tree
;;;
(defun read-continue (v s c)
  (declare (type t v)
           (type list s c)
           (values t))
  (cond ((eq *reader-void* v) (general-read s c))
        ((equal v control-d-string) (general-read-eof-error))
        (t (cons v (general-read s c)))))

;;; READ-CONTINUE-APPEND : {*standard-input*} value schema context ->
;;;   {*standard-input*} parse-tree
;;; continues the matching process; appending the value given
;;; the value is returned as the first component of the resulting tree
;;;
(defun read-continue-append (v s c)
  (declare (type t v)
           (type list s c)
           (values t))
  (cond ((eq *reader-void* v) (general-read s c))
        ((equal v control-d-string) (general-read-eof-error))
        (t (append v (general-read s c)))))

(defun general-read-show-context ()
  (declare (values t))
  (when (and *chaos-verbose*
             *reader-current-context*
             (not (eq *reader-void* *reader-current-context*)))
    (terpri)
    (princ "-- Expecting context is: ")
    (print-simple-princ-open *reader-current-context*)
    (unless *chaos-input-source* (terpri)))
  (when *chaos-input-source*            ; nil means may be from terminal
    (terpri)
    (princ "-- file: ") (princ (namestring *chaos-input-source*))
    (when (file-position *standard-input*)
      (princ "  at character position: ")
      (prin1 (file-position *standard-input*)))
    (terpri)
    (when (and *reader-current-schema*
               (general-read-is-simple-schema *reader-current-schema*))
      (princ "  expecting: ")
      (general-read-print-schema-1 *reader-current-schema* :short)
      (terpri))
    (when (and *reader-starting-position*
               (not (equal *reader-starting-position*
                           (file-position *standard-input*))))
      (princ "  starting character position was: ")
      (prin1 *reader-starting-position*)
      (terpri))
    (princ "-- Context:")
    (unless (eq *reader-void* *reader-input*)
      (princ *reader-input*))
    (if (reader-is-at-eof)
        (princ " ... at end of file")
        (dotimes (i 20)
          (print-check)
          (princ #\space)
          (let ((val (read-sym)))
            (when (at-eof)
              (princ " [end of file]")
              (return))
            (princ val)
            (when (equal "eof" val) (return)))))
    (terpri)))

#||
(defun general-read-is-simple-schema (sch)
  (declare (type t sch)
           (values (or null t)))
  (or (atom sch)
      (and (consp sch)
           (every #'atom sch)))
  )
||#

(defun general-read-is-simple-schema (sch)
  (declare (ignore sch))
  t)

;;; modify print to certain depth and length transliterating notations
;;;

(defun general-read-display-schema (sch &optional (short nil))
  (declare (type list sch)
           (values t))
  (let ((limit (if short 10 most-positive-fixnum))
        (count 0)
        (*print-level* (if short 2 nil)))
    (declare (type fixnum limit count))
    (if (> (length sch) 1)
      (dolist (i (firstn sch 3))
        (when (>= count limit) (princ " ...") (return))
        (incf count)
        (print-check)
        (princ #\space)
        (prin1 i))
    (dolist (i sch)
      (print-check)
      (princ #\space)
      (prin1 i)))))

(defun general-read-print-schema-1 (s &optional (short nil))
  (declare (type t s)
           (values t))
  (if (atom s)
      (princ s)
    (let ((flag nil))
      (declare (ignore flag))
      (general-read-print-schema (car s) short))))

(defun general-read-print-schema (s &optional (short nil))
  (declare (type t s)
           (values t))
  (let ((limit (if short 10 most-positive-fixnum))
        (count 0))
    (declare (type fixnum limit count))
    (if (atom s)
        (princ s)
      (let ((flag nil))
        (dolist (i s)
          (when (>= count limit) (princ " ...") (return))
          (incf count)
          (if (< *print-line-limit* (filecol *standard-output*))
              (progn
                (print-next)
                (when *print-indent-contin*
                  (princ "    ")
                  (setq flag t)))
            (if flag (princ " ") (setq flag t)))
          (if (atom i)
              (unless (eql control-d i)
                (prin1 i))
            (if (eq ':+ (car i))
                (dolist (e (cdr i))
                  (if (< *print-line-limit* (filecol *standard-output*))
                      (progn
                        (print-next)
                        (when *print-indent-contin*
                          (princ "    ")
                          (setq flag t)))
                    (if flag (princ " ") (setq flag t)))
                  (prin1 e))
              (prin1 i))))))))

(defun read-comment-line ()
  (let ((ch (peek-char nil *standard-input* nil nil)))
    (unless ch (return-from read-comment-line " "))
    (if (eq .reader-ch. 'return)
        (return-from read-comment-line (string #\linefeed))
        (if (member ch '(#\linefeed #\page #\return #\newline))
            (progn (read-char)
                   (return-from read-comment-line (string #\linefeed)))
            (read-line)))))

;;; an ignored comment (value is "")
;;; has provision for long case: ** ( )
;;;
(defun general-read-commentlong ()
  (declare (values simple-string))
  (let (ch)
    (unless (eql '\( .reader-ch.)
      (loop
          (setq ch (read-char *standard-input* nil *lex-eof*))
          (unless (or (eql #\Space ch)
                      (eql #\Tab ch))
            (return)))
      (setq .reader-ch.
            (if (eq ch *lex-eof*)
                *lex-eof*
                (let ((val (reader-get-syntax ch)))
                  (if val val ch)))))
    (if (eq '\( .reader-ch.)
        (lex-read)
        (unless (or (eql #\Newline ch) (eql #\Return ch)) (read-line))
        ))
  (setq .reader-ch. 'space)
  ""
  )


;;;=============================================================================
;;; SPECIAL READERS
;;; readers specific to external representations of Chaos expressions.
;;;=============================================================================


;;; READ-TERM-FROM-STRING : string -> List(Token)
;;;
;;; (declaim (function read-term-from-string (string) list))
(declaim (inline read-term-from-string))

; (eval-when (:execute :compile-toplevel :load-toplevel)
;   (defparameter .term-delimiting-chars.
;       '("[" "]" "{" "}" ";" "@" "%" "~" )))
(eval-when (:execute :compile-toplevel :load-toplevel)
  (defparameter .term-delimiting-chars. '("[" "]" "{" "}")))

(defun !set-term-delim-chars ()
  (!set-single-reader .term-delimiting-chars.))

(defun read-term-from-string (string)
  (declare (type simple-string string))
  (with-input-from-string (*standard-input* string)
    (let ((cur (!set-term-delim-chars)))
      (let ((res nil)
            (inp nil)
            (inv nil))
        (loop (setq inp (lex-read))
              (when #+:CCL-3 (equal *lex-eof* inp)
                    #-:CCL-3 (eq *lex-eof* inp)
                (setq *reader-input* inv)
                (return))
              (cond ((= 1 (length (the list inp))) (setq inv (car inp)))
                    (t (setq inv *reader-void*)))
              (setq res (append res inp))
              )
        (!set-reader cur)
        (clear-input)
        (setq *reader-input* *reader-void*)
        res
        ))))

(defun read-seq-of-term-from-string (string)
  (declare (type simple-string string)
           (values list))
  (with-input-from-string (*standard-input* string)
    (let ((cur (!set-term-delim-chars)))
      (let ((res nil))
        (block exit
          ;; read in one token.
          (if (eq *reader-input* *reader-void*)
              (setq *reader-input* (lex-read))
              (when (equal "(" *reader-input*)
                (setq *reader-input* (lex-read-rest-of-list))))
          (when (reader-is-at-eof) (return-from exit))
          (when (atom *reader-input*)
            (setq *reader-input* (list *reader-input*)))
          (loop (setq res (append res *reader-input*))
                (setq *reader-input* (lex-read))
                (when (reader-is-at-eof) (return-from exit)))
          )
        ;; restore read table.
        (!set-reader cur)
        (clear-input)
        (setq *reader-input* *reader-void*)
        res
        ))))
  
;;; READ-TERM-AT-TOP
;;;
(defun read-term-at-top (&rest ignore)
  (declare (ignore ignore))
  (let ((lines (read-lines)))
    (if (eq lines *lex-eof*)
        *lex-eof*
        (read-term-from-string lines))))
  
(defun read-seq-of-term-at-top (&rest ignore)
  (declare (ignore ignore))
  (let ((lines (read-lines)))
    (if #+:MCL (equal lines *lex-eof*)
        #-:MCL (eq lines *lex-eof*)
        *lex-eof*
        (read-seq-of-term-from-string lines))))

;;; READ-TERM
;;;
(defun read-term (context)
  (declare (type list context)
           (values list))
  (let ((cur (!set-term-delim-chars)))
    (let ((res nil)
          inp
          inv)
      (loop (setq inp (lex-read))
            (when #-:ccl-3(eq *lex-eof* inp)
                  #+:ccl-3(equal *lex-eof* inp)
                  (return-from read-term *lex-eof*))
            (cond ((= 1 (length (the list inp)))
                   (setq inv (car (the list inp))))
                  (t (setq inv *reader-void*)))
            (when (lex-string-match inv (car context))
              (setq *reader-input* inv)
              (return))
            (setq res (append res inp))
            )
      (!set-reader cur)
      res
      )))

;;; READ-SEQ-OF-TERM 
;;;
(defun read-seq-of-term (context)
  (declare (type list context)
           (values list))
  (let ((cur (!set-term-delim-chars)))
    (let ((res nil))
      ;; read in one token.
      (if (eq *reader-input* *reader-void*)
          (setq *reader-input* (lex-read))
          (when (equal "(" *reader-input*)
            (setq *reader-input* (lex-read-rest-of-list))))
      (when (at-eof-or-control-d)       ; was reader-is-at-eof
        (return-from read-seq-of-term *lex-eof*))
      (when (atom *reader-input*)
        (setq *reader-input* (list *reader-input*)))
      (loop (when (and (null (cdr *reader-input*))
                       (stringp (car *reader-input*))
                       (lex-string-match (car *reader-input*) (car context)))
              (setq *reader-input* (car *reader-input*))
              (return))
            (setq res (append res *reader-input*))
            (setq *reader-input* (lex-read))
            (when (at-eof-or-control-d) ; was reader-is-at-eof
              (return-from read-seq-of-term *lex-eof*))
            )
      ;; restore read table.
      (!set-reader cur)
      res
      )))

;;; READ-ARGS
;;;
(defun read-args (&rest context)
  (declare (ignore context))
  (let ((*live-newline* t))
    (let ((res nil)
          (inv nil)
          inp)
      (loop (setq inp (lex-read))
        (when #-:ccl-3(eq *lex-eof* inp)
              #+:ccl-3(equal *lex-eof* inp)
              (return-from read-args *lex-eof*))
        (cond ((= 1 (length (the list inp)))
               (setq inv (car (the list inp))))
              (t (setq inv *reader-void*)))
        (when (and (consp inv) (eq (car inv) .String-token.))
          (setq res (append res inp))
          (setq *reader-input* *reader-void*)
          (return))
        (when (lex-string-match inv 'return)
          (setq *reader-input* *reader-void*)
          (return))
        (setq res (append res inp)))
      res)))

;;; READ-SEQ-OF-OPNAME
;;;
; (defparameter .op-name-delimiting-chars.
;     '("[" "]" "{" "}" "_" ";" "@" "%" "~"))
(defparameter .op-name-delimiting-chars. '("[" "]" "{" "}" "_"))

(defun read-seq-of-opname (context)
  (declare (type list context)
           (values list))
  (let ((cur (!set-single-reader .op-name-delimiting-chars.)))
    (let ((res nil))
      (if (eq *reader-input* *reader-void*)
          (setq *reader-input* (lex-read))
          (when (equal "(" *reader-input*)
            (setq *reader-input* (lex-read-rest-of-list))))
      (when                             ; (reader-is-at-eof)
          (at-eof-or-control-d)
        (return-from read-seq-of-opname *lex-eof*))
      (when (atom *reader-input*)
        (setq *reader-input* (list *reader-input*)))
      (loop (when (and (null (cdr *reader-input*))
                       (stringp (car *reader-input*))
                       (lex-string-match (car *reader-input*) (car context)))
              (setq *reader-input* (car *reader-input*))
              (return))
            (setq res (append res *reader-input*))
            (setq *reader-input* (lex-read))
            (when (at-eof-or-control-d) ; (reader-is-at-eof)
              (return-from read-seq-of-opname *lex-eof*))
            )
      (!set-reader cur)
      res
      )))

;;; READ-OPNAME context
;;;
(defun read-opname (context)
  (declare (type list context)
           (values list))
  (let ((cur (!set-single-reader .op-name-delimiting-chars.)))
    (let ((res nil)
          inp
          inv)
      (loop (setq inp (lex-read))
            (when (eq *lex-eof* inp)
                  (return-from read-opname *lex-eof*))
            (cond ((= 1 (length (the list inp))) (setq inv (car inp)))
                  (t (setq inv *reader-void*)))
            (when (lex-string-match inv (car context))
              (setq *reader-input* inv)
              (return))
            (setq res (append res inp))
            )
      (!set-reader cur)
      res
      )))
  
(defun read-opname-at-top (&rest ignore)
  (declare (ignore ignore))
  (let ((line (read-lines)))
    (if (eq line *lex-eof*)
        *lex-eof*
        (read-opname-from-string line))))

(defun read-seq-of-opname-at-top (&rest ignore)
  (declare (ignore ignore))
  (let ((line (read-lines)))
    (if (eq line *lex-eof*)
        *lex-eof*
        (read-seq-of-opname-from-string line))))

(defun read-opname-from-string (string)
  (declare (type simple-string string))
  (with-input-from-string (*standard-input* string)
    (let ((cur (!set-single-reader .op-name-delimiting-chars.)))
      (let ((res nil)
            (inp nil)
            (inv nil))
        (loop (setq inp (lex-read))
              (when (eq *lex-eof* inp)
                (setq *reader-input* inv)
                (return))
              (cond ((= 1 (length (the list inp))) (setq inv (car inp)))
                    (t (setq inv *reader-void*)))
              (setq res (append res inp))
              )
        (!set-reader cur)
        (clear-input)
        (setq *reader-input* *reader-void*)
        res
        ))))

(defun read-seq-of-opname-from-string (string)
  (declare (type simple-string string)
           (values list))
  (with-input-from-string (*standard-input* string)
    (let ((cur (!set-single-reader .op-name-delimiting-chars.)))
      (let ((res nil))
        (block exit
          ;; read in one token.
          (if (eq *reader-input* *reader-void*)
              (setq *reader-input* (lex-read))
              (when (equal "(" *reader-input*)
                (setq *reader-input* (lex-read-rest-of-list))))
          (when (reader-is-at-eof) (return-from exit))
          (when (atom *reader-input*)
            (setq *reader-input* (list *reader-input*)))
          (loop (setq res (append res *reader-input*))
                (setq *reader-input* (lex-read))
                (when (reader-is-at-eof) (return-from exit)))
          )
        ;; restore read table.
        (!set-reader cur)
        (clear-input)
        (setq *reader-input* *reader-void*)
        res
        ))))
  
;;; READ-SORT
;;;
(defun read-sort (c)
  (declare (ignore c))
  (let ((old-syntax (reader-get-syntax #\!)))
    (unwind-protect
         (let ((inp nil))
           (!set-syntax #\! nil)
           (setq inp (!read-sym))
           (cond ((and (stringp inp)
                       (eql #\. (char (the simple-string inp)
                                      (1- (length (the simple-string inp))))))
                  (loop (unless (eq 'space .reader-ch.) (return)) ;a bit ugly
                        (setq .reader-ch. (reader-get-char *standard-input*)))
                  (when (eq .reader-ch. *lex-eof*)
                        (return-from read-sort *lex-eof*))
                  (if (equal '\( .reader-ch.)
                      (let ((rest (lex-read)))
                        (if (eq rest *lex-eof*)
                            *lex-eof*
                            (list* inp (lex-read))))
                      inp))
                 (t inp)
                 ))
      (!set-syntax #\! old-syntax))))

;;; READ-SORTS
;;;
(defun read-sorts (context)
  (let ((res nil)
        (old-syntax (reader-get-syntax #\!)))
    (unwind-protect
         (progn (!set-syntax #\! nil)
                (loop (!read-in)
                  (when (at-eof-or-control-d)
                    (return-from read-sorts *lex-eof*))
                  (when (lex-string-match *reader-input* (car context))
                    (return (nreverse res)))
                  (push (read-sort context) res)))
      (!set-syntax #\! old-syntax))))

;;; READ-CHARS 
;;;
(defun read-chars (context)
  (let ((res nil))
    (loop (!read-in)
      (when (at-eof-or-control-d)
        (return-from read-chars *lex-eof*))
      (when (lex-string-match *reader-input* (car context))
        (return-from read-chars (nreverse res)))
      (let ((c (!read-sym)))
        ;;(format t "~%- read-chars: sym=~s, res=~s" c res)
        (if (consp c)
            (push (car c) res)
          (push c res))))))

;;; SPECIAL READERS NOT Spported by Chaos General Reader
;;; 

(defun read-opattr (c)
  (declare (type list c)
           (values list))
  (!read-in)
  (when (at-eof-or-control-d) (return-from read-opattr *lex-eof*))
  (if (lex-string-match *reader-input* #\[)
      ;;
      ()
      ;;
      (progn
        (reader-suppress-ch c)
        nil)))

;;;
(defun read-super-exp (c)
  (declare (type list c)
           (values list))
  (let ((cur (!set-single-reader '(#\( #\)))))
    (prog1 (read-superexp c)
      (!set-reader cur))))

(defun read-superexp (c)
  (declare (type list c)
           (values list))
  (let ((res nil))
    (loop (!read-in)
          (when (at-eof-or-control-d) (general-read-eof-error))
          (when (general-read-string-matches *reader-input* c)
            (return res))
          (setq res (nconc res (read-superexpr-delimited))))
    res))

(defun read-superexpr-delimited ()
  (declare (values list))
  (!read-in)
  (when (at-eof-or-control-d) (general-read-eof-error))
  (let ((pr (assoc *reader-input* '(("(" ")"))
                   :test #'general-read-string-matches)))
    (cond ((null pr)
           (prog1 (cons *reader-input* nil)
             (!read-discard)))
          (t (let ((sym *reader-input*))
               (!read-discard)
               (let ((lst (read-superexp (cdr pr))))
                 (prog1 (cons sym (append lst (cons *reader-input* nil)))
                   (!read-discard)))))
          )))
;;;
;;; Module Expression Reader
;;;
;;; *modexp-parse-input* -- binds module expression input (list of tokens).
;;;
(defvar *modexp-parse-input* 'undef)

;;; MODEXP-SKIP : {*modexp-parse-input*} -> {*modexp-parse-input*}
;;; skip input one.
;;;
(defmacro modexp-skip () `(setq *modexp-parse-input* (cdr *modexp-parse-input*)))

;;;************
;;; Some utils__________________________________________________________________
;;;************

;;; SCAN-PRENTHESIZED-UNIT : tokens -> LIST[tokens], signal 'unbalanced
;;;
;;; (scan-parenthesized-unit '( "(" "aho" "(" "baka" "tako" ")" "manuke" ")" "baba"))
;;; ==> ("aho" "(" "baka" "tako" ")" "manuke")
;;;     ("baba")
;;; (scan-parenthesized-unit '( "(" "aho" "(" "baka" "tako" ")" "manuke" "baba"))
;;; ==> UNBALANCED
;;;     ("(" "aho" "(" "baka" "tako" ")" "manuke" "baba")
;;;
(defun scan-parenthesized-unit (tokens)
  (declare (type list tokens)
           (values (or symbol list) list))
  (if (equal "(" (car tokens))
      (let ((count 1)
            (lst (cdr tokens))
            (res nil)
            tok)
        (declare (type fixnum count))
        (loop (when (null lst) (return (values 'unbalanced tokens)))
              (setf tok (car lst)
                    lst (cdr lst))
              (when (and (= 1 count) (equal ")" tok))
                (return (values (nreverse res) lst)))
              (setf res (cons tok res))
              (if (equal "(" tok)
                  (incf count)
                  (if (equal ")" tok)
                      (decf count)))
              ))
      (values (list (car tokens)) (cdr tokens))))

(defun group-paren-units (tokens)
  (declare (type list tokens)
           (values list))
  (let ((res nil)
        (lst tokens)
        unit)
    (loop (multiple-value-setq (unit lst)
            (scan-parenthesized-unit lst))
          (when (eq 'unbalanced unit)
            (return tokens))
          (setq res (cons unit res))
          (when (null lst)
            (return (nreverse res)))
          )))

(defun check-enclosing-parens (tokens)
  (declare (type t tokens)
           (values (or null t)))
  (and (consp tokens)
       (equal "(" (car tokens))
       (multiple-value-bind (par rst)
           (scan-parenthesized-unit tokens)
         (declare (ignore par))
         (null rst))))

;;; READ-MODULE-EXP

(defun read-module-exp (context)
  (let ((cur (!set-single-reader '(#\[ #\]))))
    (prog1 (read-modexp context)
      (!set-reader cur))))

;;; read term with balanced: (/) [/] terminated by c context
;;;
(defun read-modexp (c)
  (let ((cur (!set-single-reader '("_"))))
    (let ((res nil))
      (loop (!read-in)
            (when (at-eof-or-control-d) (general-read-eof-error))
            (when (general-read-string-matches *reader-input* c)
              (return res))
            (setq res (nconc res (read-modexp-delimited))))
      (!set-reader cur)
      res
      )))

;;; also used for CafeOBJ view declaration.

(defun read-modexp-delimited ()
  (declare (values list))
  (!read-in)
  ;; (when (at-eof-or-control-d) (general-read-eof-error))
  (let ((pr (assoc *reader-input*
                   '(("view" "}") ("[" "]") ("(" ")") )
                   :test #'general-read-string-matches)))
    ;; (format t "~&*reader-input* ~s" *reader-input*)
    (cond ((null pr)
           (prog1 (cons *reader-input* nil)
             (!read-discard)))
          (t (let ((sym *reader-input*))
               (!read-discard)
               (let ((lst (read-modexp (cdr pr))))
                 (prog1 (cons sym (append lst (cons *reader-input* nil)))
                   (!read-discard)))))
          )))

;;; READ-MODEXP-FROM-STRING

(defun read-modexp-from-string (string)
  (declare (type simple-string string)
           (values list))
  (let ((*live-newline* nil))
    (with-input-from-string (*standard-input* string)
      (let ((cur (!set-single-reader '(#\[ #\] #\_ #\{ #\})))
            (res nil))
        (loop (!read-in)
          (when (at-eof-or-control-d) (return))
          (setq res (nconc res (read-modexp-delimited))))
        (!set-reader cur)
        (clear-input)
        (setq *reader-input* *reader-void*)
        res))))

#||
(defun module-print-top-level-choices ()
  (let ((flag nil))
    (dolist (i '(
                 "module" "mod" "view"  "reduce" "red"
                 "make" "test" "input" "in" "-->"
                 "**>" "--" "**" "parse" "match" "ev" "lisp"
                 "show" "sh" "set" "do" "select" "open" "close" "eof"
                 "let" "choose"
                 "quit" "q" "start" "apply" "cd" "ls" "pwd" ))
      (if (< *print-line-limit* (filecol *standard-output*))
          (progn
            (terpri)
            (when *print-indent-contin*
              (princ "    ")
              (setq flag t)))
          (if flag (princ " ") (setq flag t)))
      (princ i))))
||#

;;;
(defvar *interactive-session* nil)
(defun set-interactive () (setf *interactive-session* t))
(defun off-interactive () (setf *interactive-session* nil))

(defun wait-until-non-white (stream)
  (declare (type stream)
           (values t))
  (if (at-top-level)
      (loop (when (not (or (eq 'space .reader-ch.) (eq 'return .reader-ch.)))
              (setf *sub-prompt* t) (return))
            (if (eq 'return .reader-ch.)
                (progn
                  (when *sub-prompt*
                    (princ "> ")
                    (force-output))
                  (reader-get-char stream)
                  (when (eq #\? .reader-ch.)
                    (let ((*chaos-verbose* t))
                      (general-read-show-context)
                      (clear-input)
                      (force-output))
                    (setf .reader-ch. 'space)))
                (reader-get-char stream)))
      (loop (when (not (or (eq 'space .reader-ch.) (eq 'return .reader-ch.)))
              (return))
            (reader-get-char stream))))
;;; EOF
