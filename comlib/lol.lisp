;;;-*- Mode:Lisp; Syntax:Common-Lisp; Package:CHAOS -*-
(in-package :CHAOS)
;;;

;; Antiweb (C) Doug Hoyte

;; This is a "production" version of LOL with bug-fixes
;; and new features in the spirit of the book.

;; See http://letoverlambda.com

;; This is the source code for the book
;; _Let_Over_Lambda_ by Doug Hoyte.
;; This code is (C) 2002-2008, Doug Hoyte.
;;
;; You are free to use, modify, and re-distribute
;; this code however you want, except that any
;; modifications must be clearly indicated before
;; re-distribution. There is no warranty,
;; expressed nor implied.
;;
;; Attribution of this code to me, Doug Hoyte, is
;; appreciated but not necessary. If you find the
;; code useful, or would like documentation,
;; please consider buying the book!

(defun mkstr (&rest args)
  (with-output-to-string (s)
    (dolist (a args) (princ a s))))

(defun symb (&rest args)
  (values (intern (apply #'mkstr args))))



(defun group (source n)
  (if (zerop n) (error "zero length"))
  (labels ((rec (source acc)
             (let ((rest (nthcdr n source)))
               (if (consp rest)
                   (rec rest (cons
                               (subseq source 0 n)
                               acc))
                   (nreverse
                     (cons source acc))))))
    (if source (rec source nil) nil)))



(defun flatten (x)
  (labels ((rec (x acc)
             (cond ((null x) acc)
                   ((atom x) (cons x acc))
                   (t (rec
                        (car x)
                        (rec (cdr x) acc))))))
    (rec x nil)))



(defun fact (x)
  (if (= x 0)
    1
    (* x (fact (- x 1)))))

(defun choose (n r)
  (/ (fact n)
     (fact (- n r))
     (fact r)))




(defun g!-symbol-p (s)
  (and (symbolp s)
       (> (length (symbol-name s)) 2)
       (string= (symbol-name s)
                "G!"
                :start1 0
                :end1 2)))



(defmacro defmacro/g! (name args &rest body)
  (let ((syms (remove-duplicates
                (remove-if-not #'g!-symbol-p
                               (flatten body)))))
    `(defmacro ,name ,args
       (let ,(mapcar
               (lambda (s)
                 `(,s (gensym ,(subseq
                                 (symbol-name s)
                                 2))))
               syms)
         ,@body))))

(defun o!-symbol-p (s)
  (and (symbolp s)
       (> (length (symbol-name s)) 2)
       (string= (symbol-name s)
                "O!"
                :start1 0
                :end1 2)))

(defun o!-symbol-to-g!-symbol (s)
  (symb "G!"
        (subseq (symbol-name s) 2)))

(defmacro defmacro! (name args &rest body)
  (let* ((os (remove-if-not #'o!-symbol-p args))
         (gs (mapcar #'o!-symbol-to-g!-symbol os)))
    `(defmacro/g! ,name ,args
       `(let ,(mapcar #'list (list ,@gs) (list ,@os))
          ,(progn ,@body)))))

(defun |#`-reader| (stream sub-char numarg)
  (declare (ignore sub-char))
  (unless numarg (setq numarg 1))
  `(lambda ,(loop for i from 1 to numarg
                  collect (symb 'a i))
     ,(funcall
        (get-macro-character #\`) stream nil)))

(set-dispatch-macro-character
  #\# #\` #'|#`-reader|)

;; Nestable suggestion from Daniel Herring

(defun |#"-reader| (stream sub-char numarg)
  (declare (ignore sub-char numarg))
  (let (chars (state 'normal) (depth 1))
    (loop do
      (let ((curr (read-char stream)))
        (cond ((eq state 'normal)
                 (cond ((char= curr #\#)
                          (push #\# chars)
                          (setq state 'read-sharp))
                       ((char= curr #\")
                          (setq state 'read-quote))
                       (t
                          (push curr chars))))
              ((eq state 'read-sharp)
                 (cond ((char= curr #\")
                          (push #\" chars)
                          (incf depth)
                          (setq state 'normal))
                       (t
                          (push curr chars)
                          (setq state 'normal))))
              ((eq state 'read-quote)
                 (cond ((char= curr #\#)
                          (decf depth)
                          (if (zerop depth) (return))
                          (push #\" chars)
                          (push #\# chars)
                          (setq state 'normal))
                       (t
                          (push #\" chars)
                          (if (char= curr #\")
                            (setq state 'read-quote)
                            (progn
                              (push curr chars)
                              (setq state 'normal)))))))))
   (coerce (nreverse chars) 'string)))

(set-dispatch-macro-character
  #\# #\" #'|#"-reader|)

; This version is from Martin Dirichs

(defun |#>-reader| (stream sub-char numarg)
  (declare (ignore sub-char numarg))
  (let (chars)
    (do ((curr (read-char stream)
               (read-char stream)))
        ((char= #\newline curr))
      (push curr chars))
    (let ((pattern (nreverse chars))
          output)
      (labels ((match (pos chars)
        (if (null chars)
          pos
          (if (char= (nth pos pattern) (car chars))
              (match (1+ pos) (cdr chars))
              (match 0 (cdr (append (subseq pattern 0 pos) chars)))))))
        (do (curr
             (pos 0))
            ((= pos (length pattern)))
          (setf curr (read-char stream)
                pos (match pos (list curr)))
          (push curr output))
        (coerce
          (nreverse
            (nthcdr (length pattern) output))
          'string)))))


(set-dispatch-macro-character
  #\# #\> #'|#>-reader|)

(set-dispatch-macro-character #\# #\f
   (lambda (stream sub-char numarg)
     (declare (ignore stream sub-char))
     (setq numarg (or numarg 3))
     (unless (<= numarg 3)
       (error "Bad value for #f: ~a" numarg))
     `(declare (optimize (speed ,numarg)
                         (safety ,(- 3 numarg))))))

;;; EOF
