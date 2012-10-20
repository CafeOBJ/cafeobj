(in-package :chaos)
;;;  A Test grammar

(defparameter test-grammar-1
  '((s --> np vp      #'(lambda (np vp) (list 's np vp)))
    (np --> det n     #'(lambda (det n) (list 'np det n)))
    (np -->           #'(lambda () '(np)))
    (vp --> v np      #'(lambda (v np) (list 'vp v np)))
    (vp --> v s       #'(lambda (v s) (list 'vp v s)))))

(defparameter lexforms-1 '(det n v))

;;; (make-parser grammar lexforms '$) will generate the parser.
;;; After compiling that code, (parse <list-of-words>) invokes the parser.  E.g.
;;;
;;; ? (parse '(the man thinks the woman hates the dog $))
;;; (S (NP (DET THE) (N MAN)) (VP (V THINKS) (S (NP (DET THE) (N WOMAN)) (VP (V HATES) (NP (DET THE) (N DOG))))))

(defparameter lexicon-1 '(("the" det)
			  ("man" n)
			  ("woman" n)
			  ("cat" n)
			  ("dog" n)
			  ("loves" v)
			  ("thinks" v)
			  ("hates" v)
			  ($ $)))

(defvar test-gram1)
(eval-when (eval load)
  (setq test-gram1 (make-parser :test-gram1
				test-grammar-1
				lexforms-1
				'$)))
  
(defun parse-test-1 (words)
  (labels ((lookup (word)
                   (cadr (assoc word lexicon-1 :test #'equal)))
           (next-input ()
                       (let* ((word (pop words))
                              (cat (lookup word)))
                         (cons cat                  ; category
                               (list cat word))))   ; value
           (parse-error ()
                        (format nil "Error before ~a" words)))
    (with-in-grammar (test-gram1)
      (funcall *parse-engine* #'next-input #'parse-error)))
  )
                           


