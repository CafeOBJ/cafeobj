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
                               File: string.lisp
==============================================================================|#
#-:chaos-debug
(declaim (optimize (speed 3) (safety 0) #-GCL (debug 0)))
#+:chaos-debug
(declaim (optimize (speed 1) (safety 3) #-GCL (debug 3)))

;;; A collection of string utilities.

;;; *******
;;; Strings_____________________________________________________________________
;;; *******

;;; string-search-car
;;;  Returns the part of the string before the first of the delimiters in 
;;;  CHARACTER-BAG and the delimiter.
;;; CHARACTER-BAG can be general sequence.
;;;
(defun string-search-car (character-bag string &aux (delimiter nil))
  (declare (type simple-string string)
           (type list character-bag)
           (values simple-string (or null character)))
  ;;
  (let ((delimiter-position (position-if #'(lambda (character)
                                             (declare (type character character))
                                             (when (find character 
                                                         character-bag)
                                               (setq delimiter character)))
                                         string)))
    (values (subseq string 0 delimiter-position)
            delimiter)))

;;; string-search-cdr
;;;   Returns the part of the string after the first of the delimiters in 
;;;   CHARACTER-BAG, if any, and the delimiter. If none of the delimiters 
;;;   are found, returns NIL and NIL.

(defun string-search-cdr (character-bag string &aux (delimiter nil))
  (declare (type simple-string string)
           (type list character-bag)
           (values (or null simple-string)
                   (or null character)))
  (let ((delimiter-position (position-if #'(lambda (character)
                                             (when (find character 
                                                         character-bag)
                                               (setq delimiter character)))
                                         string)))
    (declare (type (or null fixnum) delimiter-position))
    (if delimiter-position
        (values (subseq string (1+ (the (integer 0 1024) delimiter-position)))
                delimiter)
        ;; Maybe this should be "" instead of NIL?
        (values nil delimiter))))

;;; parse-with-delimiter : String -> List[String]
;;;   Breaks LINE into a list of strings, using DELIM as a breaking point.

(defun parse-with-delimiter (line &optional (delim #\newline))
  (declare (type simple-string line)
           (values list))
  ;; what about #\return instead of #\newline?
  (let ((pos (position delim line)))
    (declare (type (or null fixnum) pos))
    (cond (pos
           (cons (subseq line 0 pos)
                 (parse-with-delimiter (subseq line (1+ pos)) delim)))
          (t
           (list line)))))

(defun parse-with-delimiter2 (line &optional (delim #\newline))
  (declare (type simple-string line)
           (values list))
  ;; what about #\return instead of #\newline?
  (let ((pos (position delim line)))
    (declare (type (or null fixnum) pos))
    (cond (pos
           (cons (subseq line 0 pos)
                 (cons (string delim)
                       (parse-with-delimiter2 (subseq line (1+ pos)) delim))))
          (t
           (list line)))))

;;; parse-with-delimiters
;;;   Breaks LINE into a list of strings, using DELIMITERS as a breaking point.

(defun parse-with-delimiters (line &optional (delimiters '(#\newline)))
  (declare (type simple-string line)
           (type list delimiters)
           (values list))
  ;; what about #\return instead of #\newline?
  (let ((pos (position-if #'(lambda (character) (find character delimiters))
                            line)))
    (declare (type (or null fixnum) pos))
    (cond (pos
           (cons (subseq line 0 pos)
                 (parse-with-delimiters (subseq line (1+ pos)) delimiters)))
          (t
           (list line)))))


;;; parallel-substitute
;;;  Makes substitutions for characters in STRING according to the ALIST. 
;;;  In effect, PARALLEL-SUBSTITUTE can perform several SUBSTITUTE
;;;  operations simultaneously.

(defun parallel-substitute (alist string)
  (declare (type simple-string string)
           (values simple-string))
  ;; This function should be generalized to arbitrary sequences and
  ;; have an arglist (alist sequence &key from-end (test #'eql) test-not
  ;; (start 0) (count most-positive-fixnum) end key).
  (if alist
      (let* ((length (length string))
             (result (make-string length)))
        (declare (simple-string result))
        (dotimes-fixnum (i length)
          (let ((old-char (schar string i)))
            (setf (schar result i)
                  (or (second (assoc old-char alist :test #'char=))
                      old-char))))
        result)
      string))

;;; parse-with-string-delimiter
;;;   Returns up to three values: the string up to the delimiter DELIM
;;;   in STRING (or NIL if the field is empty), the position of the beginning
;;;   of the rest of the string after the delimiter, and a value which, if
;;;   non-NIL (:delim-not-found), specifies that the delimiter was not found.

(defun parse-with-string-delimiter (delim string &key (start 0) end)
  (declare (type simple-string string)
           (type fixnum start)
           (type (or null fixnum) end)
           (type (or simple-string character) delim)
           (values (or null simple-string) (or null fixnum) symbol))
  ;; Conceivably, if DELIM is a string consisting of a single character,
  ;; we could do this more efficiently using POSITION instead of SEARCH.
  ;; However, any good implementation of SEARCH should optimize for that
  ;; case, so nothing to worry about.
  (setq end (or end (length string)))
  (let ((delim-pos (search delim string :start2 start :end2 end))
        (dlength (length delim)))
    (declare (type fixnum dlength))
    (cond ((null delim-pos)             
           ;; No delimiter was found. Return the rest of the string,
           ;; the end of the string, and :delim-not-found.
           (values (subseq string start end) end :delim-not-found))
          ((= delim-pos start)          
           ;; The field was empty, so return nil and skip over the delimiter.
           (values nil (+ start dlength) nil))
          ;; The following clause is subsumed by the last cond clause,
          ;; and hence should probably be eliminated.
          (t                            
           ;; The delimiter is in the middle of the string. Return the
           ;; field and skip over the delimiter. 
           (values (subseq string start delim-pos)
                   (+ delim-pos dlength)
                   nil)))))

;;; parse-with-string-delimiter*
;;;  Breaks STRING into a list of strings, each of which was separated
;;;  from the previous by DELIM. If INCLUDE-LAST is nil (the default),
;;;  will not include the last string if it wasn't followed by DELIM
;;;  (i.e., \"foo,bar,\" vs \"foo,bar\"). Otherwise includes it even if
;;;  not terminated by DELIM. Also returns the final position in the string.

(defun parse-with-string-delimiter* (delim string &key (start 0) end
                                           include-last)
  (declare (type simple-string string)
           (type fixnum start))
  (setq end (or end (length string)))
  (let (result)
    (loop
     (if (< start (the fixnum end))
         (multiple-value-bind (component new-start delim-not-found)
             (parse-with-string-delimiter delim string :start start :end end)
           (when delim-not-found 
             (when include-last
               (setq start new-start)
               (push component result))
             (return))
           (setq start new-start)
           (push component result))
         (return)))
    (values (nreverse result) 
            start)))

;;; split-string
;;;  Splits the string into substrings at spaces.
;;;
(defun split-string (string &key (item #\space) (test #'char=))
  (declare (type simple-string string)
           (type character item)
           (type function test)
           (values list))
  (let ((len (length string))
        (index 0)
        (result nil))
    (declare (type fixnum index len))
    (dotimes (i len (progn (unless (= index len)
                             (push (subseq string index) result))
                           (reverse result)))
      (declare (type fixnum i))
      (when (funcall test (char string i) item)
        (unless (= index i);; two spaces in a row
          (push (subseq string index i) result))
        (setf index (1+ i))))))

;;; extract-strings
;;;   Breaks STRING into a list of strings, using DELIMITERS as a 
;;;   breaking point.

(defun extract-strings (string &optional (delimiters '(#\newline #\space
                                                       #\return #\tab)))
  (declare (type simple-string string)
           (type list delimiters)
           (values list))
  (let* ((begin (position-if-not #'(lambda (character)
                                     (find character delimiters))
                                 string))
         (end   (when begin
                  (position-if #'(lambda (character)
                                   (find character delimiters))
                               string :start begin))))
    (cond ((and begin end)
           (cons (subseq string begin end)
                 (extract-strings (subseq string (1+ end)) delimiters)))
          (begin
           (list (subseq string begin)))
          (t
           nil))))

;;; format-justified-string
;;;
(defun format-justified-string (prompt contents &optional (width 80)
                                       (stream *standard-output*))
  (declare (type simple-string prompt contents)
           (type fixnum width)
           (type stream stream))
  (let ((prompt-length (+ 2 (the fixnum (length prompt)))))
    (declare (type fixnum prompt-length))
    (cond ((< (+ prompt-length (the fixnum (length contents))) width)
           (format stream "~%~A- ~A" prompt contents))
          (t
           (format stream "~%~A-" prompt)
           (do* ((cursor prompt-length)
                 (contents (split-string contents) (cdr contents))
                 (content (car contents) (car contents))
                 (content-length (1+ (the fixnum (length content)))
                                 (1+ (the fixnum (length content)))))
               ((null contents))
             (declare (type fixnum content-length))
             (cond ((< (+ cursor content-length) width)
                    (incf cursor content-length)
                    (format stream " ~A" content))
                   (t
                    (setf cursor (+ prompt-length content-length))
                    (format stream "~%~A  ~A" prompt content)))))))
  (finish-output stream))

;;; number-to-string
;;;
(defun number-to-string (number &optional (base 10))
  (declare (type fixnum number)
           (type fixnum base))
  (cond ((zerop number) "0")
        ((eql number 1) "1")
        (t
         (do* ((len (1+ (truncate (log number base)))) 
               (res (make-string len))
               (i (1- len) (1- i))
               (q number)               ; quotient
               (r 0))                   ; residue
             ((zerop q)                 ; nothing left
              res)
           (declare (simple-string res)
                    (fixnum len i r))
           (multiple-value-setq (q r) (truncate q base))
           (setf (schar res i) 
                 (schar "0123456789ABCDEFGHIJKLMNOPQRSTUVWXYZ" r))))))

;;; null-string
;;;  Returns T if STRING is the null string \"\" between START and END.

(defun null-string (string &optional (start 0) end)
  (declare (type simple-string string))
  (unless end (setf end (length string)))
  (string-equal string "" :start1 start :end1 end))

;;; read-delimited-string
;;;   Read a stream until one of the delimiters (a list of characters) is found.
;;;   Returns the characters so read until the delimiter as a string, plus the
;;;   additional values: EOF-VALUE, which is as passed if eof was reached, and
;;;   the delimiter that caused termination of the string. If EOF-ERROR-P is 
;;;   non-nil (the default), then an EOF causes an error to be signalled instead
;;;   of returning EOF-VALUE.

;; (declaim (function read-delimited-string (list stream atom t) 
;;                 (values string t character)))

(defun read-delimited-string (delimiters &optional (stream *standard-input*)
                                         (eof-error-p t) eof-value)
  (declare (type list delimiters)
           (type stream stream))
  (let (char-list)
    ;; (declare (dynamic-extent char-list))
    (do ((peeked-char (peek-char nil stream eof-error-p :eof)
                      (peek-char nil stream eof-error-p :eof)))
        ((or (member peeked-char delimiters) (eq peeked-char :eof))
         (values (coerce (nreverse char-list) 'string)
                 (if (eq peeked-char :eof) eof-value) peeked-char))
      (push (read-char stream t)
            ;; it should be good, else peek-char would have gotten the error.
            ;; so go for it.
            char-list))))

;;; numeric-char-p
;;;
(defmacro numeric-char-p (char)
  `(let ((cc (char-code ,char)))
     (and (>= cc (char-code #\0))
          (<= cc (char-code #\9)))))

;;; EOF
