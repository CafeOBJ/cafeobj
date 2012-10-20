(in-package :chaos)

(defun parser-get-rest-of-parenthesized-expr (token-list module)
  (declare (type list token-list)
	   (type module module))
  (let ((terletox-list (parse-term token-list
				   module
				   parser-max-precedence
				   *cosmos*))
	(terletox-list-prime nil)	; accumulator--to be returned in the end
	terletox)
    (declare (type list terletox-list))
    ;; this is "over-general"
    ;; group terms together with same remaining token list
    ;; check for possible term qualification, if present treat
    ;; group of terms as a unit
    (loop (when (null terletox-list) (return terletox-list-prime))
	  (setq terletox (car terletox-list))
	  (setq terletox-list (cdr terletox-list))
	  (let ((token-list (cdr terletox))
		(chaos-terms (list (caar terletox)))
		(rest-terletox-list nil))
	    (dolist (tlt terletox-list)
	      (if (eq (cdr tlt) token-list)
		  (push (caar tlt) chaos-terms) ;use rplacd for space ??
		  (push tlt rest-terletox-list)))
	    (setq terletox-list rest-terletox-list)
	    ;; for each solution, try to swallow ")";
	    (if (equal (car token-list) ")")
		;; token-list is not empty and begins with ")":
		;; then:  ;swallow ")", set precedence level to 0, and accumulate:
		(if (and (cdr token-list)
			 (let ((fst (char (the simple-string
					    (cadr token-list))
					  0)))
			   (eql #\. fst)
			   #||
			   (or (eql #\. fst)
			       (eql #\: fst))
			   ||#
			   ))
		    ;; !! might modify this last condition a bit
		    (multiple-value-bind (terms toks)
			(parser-scan-qualification chaos-terms
						   (cdr token-list))
		      (dolist (tm terms)
			(setq terletox-list-prime
			      (cons (cons (cons tm parser-min-precedence)
					  toks)
				    terletox-list-prime))))
		    ;; else: there isn't a qualification; create continuations
		    (dolist (tm chaos-terms)
		      (setq terletox-list-prime
			    (cons (cons (cons tm parser-min-precedence)
					(cdr token-list))
				  terletox-list-prime))))
		nil)))))

(defun parser-scan-qualification (chaos-terms token-list)
  (declare (type list chaos-terms token-list))
  (let ((tokens (if			; (member (car token-list) '("." ":") :test #'equal)
		 (member (car token-list) '(".") :test #'equal)
		    (cdr token-list)
		    (cons (subseq (the simple-string (car token-list))
				  1)
			  (cdr token-list))))
	(res nil)
	qualifier
	rest)
    (if (equal "(" (car tokens))
	(let ((paren-pair (parser-scan-parenthesized-unit tokens)))
	  (declare (type list paren-pair))
	  (if (null paren-pair) (setq res 'unbalanced)
	      (setq qualifier (if (atom (car paren-pair))
				  (list (car paren-pair))
				  (car paren-pair))
		    rest (cdr paren-pair))))
	(setq qualifier (list (car tokens))  rest (cdr tokens)))
    (if (eq 'unbalanced res) (values chaos-terms token-list)
	(let ((modval (find-module-or-error
		       (normalize-modexp (parse-modexp qualifier)))))
	  (if (or (null modval)
		  (modexp-is-error modval))
	      (values chaos-terms token-list) ; no.....
	      (let ((exact nil)
		    (res nil)
		    tm)
		(loop (when (null chaos-terms) (return))
		      (setq tm (car chaos-terms))
		      (setq chaos-terms (cdr chaos-terms))
		      (when (if (term-is-variable? tm)
				(member (term-sort tm)
					(module-all-sorts modval))
				(if (term-is-builtin-constant? tm)
				    (member (term-sort tm) (module-all-sorts modval))
				    (let ((head (term-head tm)))
				      (dolist (ops (module-all-operators modval))
					(when (memq head (opinfo-methods ops))
					  (return t))))))
			(if res
			    (progn (setq exact t) (push tm res) (return))
			    (push tm res))))
		(if exact
		    (let ((oldres res))
		      (setq res nil)
		      (dolist (tm oldres)
			(when (if (term-is-variable? tm)
				  (eq modval (sort-module (term-sort tm)))
				  (eq modval (operator-module (method-operator
							       (term-head tm)))))
			  (push tm res)))
		      (dolist (tm chaos-terms)
			(when (if (term-is-variable? tm)
				  (eq modval(sort-module (term-sort tm)))
				  (eq modval (operator-module (method-operator
							       (term-head tm)))))
			  (push tm res)))))
		(values res rest)))))))

(defun pre-choose-final (module final)
  (declare (type module module)
	   (type list final))
  ;; here we minimize the set of candidates of possible result of parsing.
  ;; 
  (let ((well )
	(min nil)
	(so (module-sort-order module))
	(res nil))
    (declare (type list well res min)
	     (type sort-order so))
    ;; due to our parsing algorithm (no flames are welcom), possibly
    ;; the same (in a sense of term-is-similar?) terms can co-exist.
    (setq final (delete-duplicates final :test #'term-is-similar?))

    ;; of course, ill sorted terms detected during parsing procs. are
    ;; out of our focus. 
    ;; miserablly terminates when all are ill-defined terms...
    (setq well (remove-if #'(lambda (x)
			     (not (term-is-really-well-defined x)))
			  final)) 
    (unless well (return-from pre-choose-final final))

    ;; select the lowest parses among possibilities.
    ;; this might be redundant because we has been trying to get the
    ;; lowest operator so far.
    (setf min (minimal-sorts (mapcar #'(lambda (x) (term-sort x)) well)
			     so))
    (dolist (f well)			; filter out terms with
					; non-minimal sort. 
      (when (memq (term-sort f) min)
	(push f res)))

    ;; special case for terms of *universal-sort*, they may have some
    ;;; ill-formed terms in their subterms.

    (if (or (sort= (car min) *cosmos*)
	    (sort= (car min) *universal-sort*)
	    (sort= (car min) *huniversal-sort*))
	(let ((pres (remove-if #'(lambda (x)
				   (and (term-is-application-form? x)
					(some #'term-contains-error-method
					      (term-subterms x))))
			       res)))
	  (if pres
	      ;; if there are some remaining terms serviving these
	      ;; hard checks, they can be the result.
	      pres
	      ;; OK, we failed in a test. let ask users which we should 
	      ;; take as a result.
	      res))
	res)))

(defun method-w= (m1 m2)
  (or (method= m1 m2)
      (when (and (sort= (method-coarity m1) *sort-id-sort*)
		 (sort= (method-coarity m2) *sort-id-sort*))
	(equal (method-symbol m1) (method-symbol m2)))))

(defun term-is-similar? (t1 t2)
  (declare (type term t1)
	   (type (or term null) t2)
	   (values (or null t)))
  (or (term-eq t1 t2)
      (if t2
	  (let ((t1-body (term-body t1))
		(t2-body (term-body t2)))
	    (cond ((term$is-application-form? t1-body)
		   (and (term$is-application-form? t2-body)
			(if (method-w= (term$head t1-body) (term$head t2-body))
			    (let ((subs1 (term$subterms t1-body))
				  (subs2 (term$subterms t2-body)))
			      (loop
			       ;; (when (null subs1) (return (null subs2)))
			       (when (null subs1) (return t))
			       (unless (term-is-similar? (car subs1) (car subs2))
				 (return nil))
			       (setq subs1 (cdr subs1)  subs2 (cdr subs2))))
			    nil)))
		  ((term$is-variable? t1-body)
		   (and (term$is-variable? t2-body)
			(eq (variable$name t1-body)
			     (variable$name t2-body))
			(sort= (variable$sort t1-body)
			       (variable$sort t2-body))))
		  ((term$is-variable? t2-body) nil)
		  ((term$is-builtin-constant? t1-body)
		   (term$builtin-equal t1-body t2-body))
		  ((term$is-builtin-constant? t2-body) nil)
		  ((term$is-lisp-form? t1-body)
		   (and (term$is-lisp-form? t2-body)
			(equal (term$lisp-form-original-form t1-body)
			       (term$lisp-form-original-form t2-body))))
		  ((term$is-lisp-form? t2-body) nil)
		  (t (break "unknown type of term." )))))))
;;; EOF
