;;;-*- Mode:LISP; Package:CHAOS; Base:10; Syntax:Common-lisp -*-
;;; $Id: trans-decl.lisp,v 1.4 2007-02-05 04:35:51 sawada Exp $
(in-package :chaos)
#|==============================================================================
                             System: CHAOS
                            Module: cafeobj
                          File: trans-decl.lisp
==============================================================================|#
#-:chaos-debug
(declaim (optimize (speed 3) (safety 0) #-GCL (debug 0)))
#+:chaos-debug
(declaim (optimize (speed 1) (safety 3) #-GCL (debug 3)))

;;;== DESCRIPTION ==============================================================
;;; Translators of (partially parsed) CafeOBJ extenal representation form to
;;; internal representations (CHAOS abstract syntax). 
;;; Very dirty (ad hoc) codes, this is because that the result of the current
;;; top level parser are only vaguely defined, and the poor power of the parser
;;; forces  the concrete syntax of CafeOBJ be dirty one. Even for an one
;;; syntactic category, it can be parsed in different manner according to the
;;; context it appears! Very sad situation. Must be fixed soon! 
;;;
;;; ** NOTE ********************************************************************
;;; As mentioned above, if the current implementation of the CafeOBJ top level
;;; parser were more well done, the translators would be no more needed, or
;;; would be more clean. This should be done in the near future.
;;; ****************************************************************************

;;; ***************
;;; INTERFACE  FORM____________________________________________________________
;;; ***************

;;; PARSE-INTERFACE-DECL scans the interface expression and produces the internal
;;; form of importation expressions.
;;;
(defun parse-interface-decl (decl-form &rest ignore)
  (declare (ignore ignore))
  (when decl-form
    (let ((args nil)
          (lst (cdr decl-form)))
      (loop (unless (cdr lst) (return))
        (let ((tag (car lst))
              (mode "protecting"))
          (when (member tag '("pr" "protecting" "ex" "extending" "us" "using"
                              "inc" "including")
                        :test #'equal)
            (setf lst (cdr lst))
            (setf mode tag))
          (dolist (nm (car lst))
            (setf args
              (nconc args (process-importation-form
                           (cons mode
                                 (cons nm
                                       (list (cadr lst)
                                             (caddr lst))))))))
          ;;
          (setq lst (cddddr lst))))
      args)))

;;; PROCESS-IMPORTATION-FORM scans the parsed importation expression and
;;; produces the internal form of importation expression.
;;; For an example, 
;;;    protecting (X :: FOO * { sort Bar -> Bar' })
;;; will be translated to 
;;;    (%import :protecting (%* "FOO" ((sort "Bar" "Bar'"))) "X")
;;;
(defun process-importation-form (imp-expr &rest ignore)
  (declare (ignore ignore))
  (macrolet ((scan-modexp (__exp)
               ` (let ((*__modexp nil))
                   (loop (when (or (null ,__exp)
                                   (null (car ,__exp))
                                   (equal (car ,__exp) ","))
                           (return))
                     (push (car ,__exp) *__modexp)
                     (setf ,__exp (cdr ,__exp)))
                   (flatten-list (nreverse *__modexp)))))
    (let ((mode (case-equal (car imp-expr)
			    (("pr" "protecting") :protecting)
			    (("ex" "extending") :extending)
			    (("us" "using") :using)
			    (("inc" "including") :including)))
	  (alias nil)
	  (expr nil)
	  (res nil))
      ;;
      (cond ((equal (second imp-expr) "(")
	     (setq expr (scan-parenthesized-unit (cdr imp-expr))))
	    ((and (consp (second imp-expr))
		  (equal "as" (car (second imp-expr))))
	     (setq alias (second (second imp-expr)))
	     (setq expr (if (equal (third imp-expr) "(")
			    (scan-parenthesized-unit (cddr imp-expr))
			  (cddr imp-expr))))
	    (t (setq expr (cdr imp-expr))))
      ;;
      (loop (unless expr (return))
        (if (equal (second expr) "::")
            ;; parameterized importation
            (let ((param (first expr)))
              (when (find-if #'(lambda (x)
                                 (or (eql x #\.) (eql x #\@)))
                             param)
                (with-output-chaos-error ()
                  (format t "parameter name must not contain `.' or `@'.")
                  ))
              (setf expr (cddr expr))
              (push (%make-import :mode mode
                                  :parameter param
                                  :module (parse-modexp (scan-modexp expr))
				  :alias alias)
                    res))
          ;; non parameterized importation
          (push (%make-import :mode mode
                              :module (parse-modexp (scan-modexp expr))
			      :alias alias)
                res))
        (setf expr (cdr expr)))
      ;;
      (nreverse res))))

;;; *****************************
;;; SORT/SUBSORT DECLARATION FORM_______________________________________________
;;; *****************************

;;; PROCESS-SORT-REFERENCE-FORM:
;;; the translator of sort reference.
;;; uses module expression parser (`do-parse-sort-ref').
;;;
(defun process-sort-reference-form (tokens &rest ignore)
  (declare (ignore ignore))
  (flet ((report-trans-err (&rest ignore)
           (declare (ignore ignore))
           (with-output-msg ()
             (format t "could not parse tokens:~{~^ ~a~}" tokens)
             (chaos-error 'parse-err))))
    (if (null tokens)
        nil
      (progn
        (when (atom tokens)
          (setf tokens (list tokens)))
        (let ((*modexp-parse-input* tokens))
          (with-chaos-error (#'report-trans-err)
            (let ((val (do-parse-sort-ref nil)))
              (if (null *modexp-parse-input*)
                  val
                nil))))))))

;;; PROCESS-SORT-AND-SUBSORT-FORM
;;;
(defun process-sort-and-subsort-form (decl &optional hidden)
  (let ((forms nil)
        (form nil)
        (res nil))
    (dolist (elt (cdr decl))
      (cond ((or (atom elt)
                 (equal (car elt) ","))
             (push form forms)
             (setf form nil))
            (t (dolist (x elt)
                 (if (equal x "<")
                     (setf form (append form '(:<)))
                   (setf form (append form (list x))))))
            ))
    (when *on-debug*
      (format t "~&sort_decl: forms = ~a" forms))
    (dolist (f (nreverse forms))
      (cond ((memq ':< f)
             ;; subsort declaration.
             (setf f (mapcar #'(lambda (x)
                                 (if (eq x ':<)
                                     ':<
                                   (process-sort-reference-form x)))
                             f))
             (push (%subsort-decl* (cons hidden f))
                   res))
            (t
             ;; sort declaration.
             (dolist (e f)
               (push (%sort-decl* (process-sort-reference-form e)
                                  hidden)
                     res)))))
    ;; 
    (nreverse res)))

;;; Hidden sort/subsort declaration
;;;
(defun process-hidden-sort-form (decl-form &rest ignore)
  (declare (ignore ignore))
  (let ((decl (cadr decl-form)))
    (case-equal (car decl)
                ("[" 
                 (process-sort-and-subsort-form decl t))
                ("record"
                 (list (process-record-declaration-form decl t)))
                ("class"
                 (list (process-class-declaration-form decl t)))
                (t (with-output-panic-message ()
                     (format t "Unknown type of hidden declaration ~s." (car decl)))))))

;;; **********************
;;; BSORT DECLARATION FORM______________________________________________________
;;; **********************
(defun process-bsort-declaration (decl &rest ignore)
  (declare (ignore ignore))
  (let ((sort-name (cadr decl))
        (lisp-info (caddr decl)))
    (if lisp-info
        (%make-bsort-decl :name sort-name
                          :token-predicate (first lisp-info)
                          :term-creator (second lisp-info)
                          :term-printer (third lisp-info)
                          :term-predicate (fourth lisp-info))
      (%make-bsort-decl :name sort-name))))

;;; Hidden builtin sort

(defun process-hbsort-declaration (decl &rest ignore)
  (declare (ignore ignore))
  (let ((sort-name (cadr decl))
        (lisp-info (caddr decl)))
    (if lisp-info
        (%make-bsort-decl :name sort-name
                          :hidden t
                          :token-predicate (first lisp-info)
                          :term-creator (second lisp-info)
                          :term-printer (third lisp-info)
                          :term-predicate (fourth lisp-info))
      (%make-bsort-decl :hidden t :name sort-name))))

;;; ******************************
;;; RECORD/ CLASS DECLARATION FORM______________________________________________
;;; ******************************
;;; record decl form ::= ("record" "R1" (super-refs)  "{" slot-decls "})
;;;                           0     1         2        3      4
;;;                    | ("record" "R2" "{" slot-decls "}")
;;; super-refs ::= ( "[" 
;;; ("s-1" (":" "Nat") "," "s-2" ("=" "(" ("213") ")")) "}")
;;; 
;;;      0      1    2  
;;;-----------------------------------------------------------------------------

(defun gather-slot-decls (decl-form &rest ignore)
  (declare (ignore ignore))
  (if (atom decl-form)
      nil
    (let ((res nil)
          (elt nil)
          (forms decl-form))
      (loop (unless forms (return))
        (let ((f (car forms)))
          ;; dirty work
          (cond ((member f '("--" "**") :test #'equal)
                 (setf forms (cddr forms)))
                ((equal f "-->")
                 (format t "~&-- ~a~%" (cadr forms))
                 (setf forms (cddr forms)))
                ((equal f "**>")
                 (format t "~&** ~a~%" (cadr forms))
                 (setf forms (cddr forms)))
                (t (push (list f (cadr forms)) res)
                   (setf forms (cddr forms))))))
      (dolist (e res)
        (let ((sort-ref nil)
              (default-value nil))
          (if (equal (caadr e) ":")     ; (first (second e))
              (setf sort-ref (cadr (second e)))
            (progn
              (setf sort-ref (car (last (second e))))
              (setf default-value (third (second e)))))
          (push (%slot* (car e)
                        (process-sort-reference-form sort-ref)
                        default-value)
                elt)))
      elt)))

(defun process-super-refs (supers &rest ignore)
  (declare (ignore ignore))
  (let ((res nil))
    (dolist (sup supers)
      (when (consp sup)
        (if (cdr sup)
            (let ((rmap nil)
                  r-tokens)
              (unless (equal "*" (cadr sup))
                (with-output-chaos-error ()
                  (format t "Unknown super reference ~a" (cadr sup))
                  ))
              ;; slot renaming
              ;; NOTE: now does not check most of syntactic errors.
              (setf r-tokens (scan-parenthesized-unit (cddr sup)))
              (do ((ren r-tokens (cddddr ren)))
                  ((null ren))
                (if (equal (second ren) "->")
                    (push (%attr-rename* (first ren) (third ren))
                          rmap)
                  (with-output-chaos-error ()
                    (format t "invalid super slot renaming ~a" ren)
                    )))
              (push (%super* (process-sort-reference-form (car sup))
                             (nreverse rmap))
                    res))
          (push (%super* (process-sort-reference-form sup)
                         nil)
                res))))
    (nreverse res)))

(defun process-record-declaration-form (r &rest ignore)
  (declare (ignore ignore))
  (let* ((name (nth 1 r))
         (supers (if (equal (nth 3 r) "{")
                     (process-super-refs (nth 2 r))
                   nil))
         (slot-decls (if supers
                         (gather-slot-decls (nth 4 r))
                       (gather-slot-decls (nth 3 r)))))
    ;; (declare-record-in-module *current-module* name supers slot-decls)
    (%record-decl* name
                   supers
                   slot-decls
                   nil)))

(defun process-class-declaration-form (r &rest ignore)
  (declare (ignore ignore))
  (let* ((name (nth 1 r))
         (supers (if (equal (nth 3 r) "{")
                     (process-super-refs (nth 2 r))
                   nil))
         (slot-decls (if supers
                         (gather-slot-decls (nth 4 r))
                       (gather-slot-decls (nth 3 r)))))
    ;; (declare-class-in-module *current-module* name supers slot-decls)
    (%class-decl* name
                  supers
                  slot-decls
                  nil)))

;;; *************************
;;; OPERATOR DECLARATION FORM___________________________________________________
;;; *************************
;;; input form: ("op" ( operator names ) ":" ( sort refs ... ) "->" sort-ref
;;;                   ("{" attributes "}" ))
;;;
(defun process-operator-declaration-form (e &rest ignore)
  (declare (ignore ignore))
  (let ((type (car e))
        (pat (let ((val (nth 1 e)))
               (if (atom val)
                   (list val)
                 (if (check-enclosing-parens val)
                     (butlast (cdr val))
                   val))))
        (flg (equal "->" (nth 3 e))))
    (when (or (null pat) (equal '(nil) pat))
      (with-output-chaos-warning ()
        (princ "operator name is empty, declaration ignored.")
        (return-from process-operator-declaration-form nil)))
    (when (equal '("_") pat)
      (with-output-chaos-warning ()
        (princ "operator pattern is just _, declaration ignored.")
        (return-from process-operator-declaration-form nil)))
    (let ((arity (mapcar #'(lambda (x)
                             (process-sort-reference-form x))
                         (if flg nil (nth 3 e))))
          (coarity (process-sort-reference-form (nth (if flg 4 5) e)))
          (attr (process-opattr-form (cadr (nth (if flg 5 6) e)))))
      ;; check mixfix op decl.
      (let ((args 0))
        (declare (type fixnum args))
        (dolist (p pat)
          (when (equal p "_")
            (incf args)))
        (unless (= 0 args)
          (unless (= args (length arity))
            (with-output-chaos-warning ()
              (format t "# of arguments mismatch for mixfix operator `~{~a~}', ignored."
                      pat)
	      (format t "~% arity = ~a, coarity=~a" arity coarity)
	      ;;
              (return-from process-operator-declaration-form nil))
            )
          )
        )
      ;;
      (if (equal type "op")
          (%make-op-decl  :name pat
                          :arity arity
                          :coarity coarity
                          :attribute attr
                          :hidden nil)
        (%make-op-decl  :name pat
                        :arity arity
                        :coarity coarity
                        :attribute attr
                        :hidden :hidden)))))

;;; pred op-pattern : arity [ attr ]
;;;
(defun process-predicate-declaration-form (e &rest ignore)
  (declare (ignore ignore))
  (let ((type (car e))
        (pat (let ((val (nth 1 e)))
               (if (atom val)
                   (list val)
                 (if (check-enclosing-parens val)
                     (butlast (cdr val))
                   val)))))
    (when (or (null pat) (equal '(nil) pat))
      (with-output-chaos-warning ()
        (princ "predicate name is empty, declaration ignored.")
        (return-from process-predicate-declaration-form nil)))
    (when (equal '("_") pat)
      (with-output-chaos-warning ()
        (princ "operator pattern is just _, declaration ignored.")
        (return-from process-predicate-declaration-form nil)))
    (let ((arity (mapcar #'(lambda (x)
                             (process-sort-reference-form x))
                         (nth 3 e)))
          (coarity "Bool")
          (attr (process-opattr-form (cadr (nth 4 e)))))
      (case-equal type
                  ("pred"
                   (%make-op-decl :name pat
                                  :arity arity
                                  :coarity coarity
                                  :attribute attr
                                  :hidden nil))
                  ("bpred"
                   (%make-op-decl :name pat
                                  :arity arity
                                  :coarity coarity
                                  :attribute attr
                                  :hidden :hidden))
                  (t
                   (with-output-panic-message ()
                     (format t "unknown predicate type ~a" type)))))))

;;; OPS
(defun process-operators-declaration-form (decl &rest ignore)
  (declare (ignore ignore))
  (mapcar #'(lambda (pat)
              (process-operator-declaration-form
               (list* "op" (if (consp pat) pat (list pat)) (cddr decl))))
          (group-paren-units (cadr decl))))

;;; BOPS
(defun process-boperators-declaration-form (decl &rest ignore)
  (declare (ignore ignore))
  (mapcar #'(lambda (pat)
              (process-operator-declaration-form
               (list* "bop" (if (consp pat) pat (list pat)) (cddr decl))))
          (group-paren-units (cadr decl))))

(defun parse-rew-strategy (strat_decl &rest ignore)
  (declare (ignore ignore))
  (let ((strats (if (member (car strat_decl)
                            '("strat" "strat:" "strategy" "strategy:")
                            :test #'equal)
                    (if (equal ")" (caddr strat_decl))
                        nil
                      (caddr strat_decl))
                  (if (equal ")" (cadr strat_decl))
                      nil
                    (cadr strat_decl)))))
    (if strat_decl
        (mapcar 'read-from-string strats)
      nil)))

(defun process-opattr-form (attrs &rest ignore)
  (declare (ignore ignore))
  (let ((theory nil)
        (assoc nil)
        (prec nil)
        (strat nil)
        (memo nil)
        (constr nil)
        (coherent nil)
        (meta-demod nil))
    (dolist (att attrs)
      (case-equal (car att)
                  (("assoc" "associative")
                   (push ':assoc theory))
                  (("commu" "comm" "commutative")
                   (push ':comm theory))
                  (("idem" "idempotent")
                   (push ':idem theory))
                  ("id:"
                   (push (list ':id (second att)) theory))
                  ("idr:"
                   (push (list ':idr (second att)) theory))
                  ("l-assoc"
                   (setf assoc :l-assoc))
                  ("r-assoc"
                   (setf assoc :r-assoc))
                  (("strat:" "strategy:" "strat" "strategy")
                   (setf strat (parse-rew-strategy att)))
                  (("prec:" "precedence:" "prec" "precedence")
                   (setf prec (read-from-string (second att))))
                  ("memo" (setf memo t))
                  (("constr" "ctor" "constructor")(setf constr t))
                  (("coherent" "beh-coherent") (setf coherent t))
                  (("demod" "meta-demod") (setq meta-demod t))
                  (t (with-output-chaos-error ()
                       (format t "unknown operator attribute ~a" att)
                       ;; (break)
                       ))))
    (%make-opattrs :theory (nreverse theory)
                   :assoc assoc
                   :prec prec
                   :strat strat
                   :memo memo
                   :constr constr
                   :coherent coherent
                   :meta-demod meta-demod)))

;;; ***********************************
;;; OPERATOR ATTRIBUTE DECLARATION FORM ________________________________________
;;; ***********************************
;;; input form: '("attr" (opname) ("{" attributes "}"))
;;;
(defun process-opattr-declaration-form (decl &rest ignore)
  (declare (ignore ignore))
  (let ((pat (let ((val (nth 1 decl)))
               (if (atom val)
                   (list val)
                 (if (check-enclosing-parens val)
                     (butlast (cdr val))
                   val))))
        (attrs (nth 3 decl)))
    (multiple-value-bind (op-id num-args)
        (implode-op-ref pat)
      (%make-opattr-decl :opref (%make-opref :name op-id
                                             :num-args num-args)
                         :attribute (process-opattr-form attrs)))))

;;; *************************
;;; VARIABLE DECLARATION FORM___________________________________________________
;;; *************************
;;; input form: '("vars" ( variable-name ... ) ":" sort-ref)
;;;                 0           1               2     3
;;;             '("var"  variable-name         ":" sort-ref)
;;;
;;; returns internal form of variable :  (%variable ( names ... ) sort)
;;;
(defun process-variable-declaration-form (decl &rest ignore)
  (declare (ignore ignore))
  (let ((sort-ref (nth 3 decl))
        (var-names (cadr decl)))
    (when (atom var-names)
      (setq var-names (list var-names)))
    (setf sort-ref (process-sort-reference-form sort-ref))
    (%var-decl* var-names sort-ref)))

(defun process-pseud-variable-declaration-form (decl &rest ignore)
  (declare (ignore ignore))
  (let ((sort-ref (nth 3 decl))
        (var-names (cadr decl)))
    (when (atom var-names)
      (setq var-names (list var-names)))
    (setf sort-ref (process-sort-reference-form sort-ref))
    (%pvar-decl* var-names sort-ref)))

;;; **********************
;;; AXIOM DECLARATION FORM______________________________________________________
;;; **********************
;;;
;;; input form : (kind ([ label ] lhs tokens ) ( rhs tokens )
;;;               [ "if" ( condition tokens ) ])
;;;  kind is one of "eq", "ceq" "cq" "rule" "rl" "crule" "crl"
;;;
(defun process-axiom-form (decl &rest ignore)
  (declare (ignore ignore))
  (let (type
        (cond-p nil)
        lhs
        rhs
        cond
        (behavioural nil)
        labels)
    (case-equal (car decl)
                ("eq" (setq type ':equation))
                (("cq" "ceq")
                 (setf type ':equation)
                 (setf cond-p t))
                (("beq" "bq")
                 (setq type ':equation)
                 (setq behavioural t))
                (("bceq" "bcq")
                 (setq type ':equation)
                 (setq behavioural t)
                 (setq cond-p t))
                (("rule" "rl" "trans" "trns")
                 (setf type ':rule))
                (("crule" "crl" "ctrans" "ctrns")
                 (setf type ':rule)
                 (setf cond-p t))
                (("brl" "brule" "btrans" "btrns")
                 (setq type ':rule)
                 (setq behavioural t))
                (("bcrl" "bcrule" "bctrans" "bctrns")
                 (setq type ':rule)
                 (setq cond-p t)
                 (setq behavioural t)))
    (setf lhs (second decl))
    (setf rhs (fourth decl))
    (setf cond (if cond-p (sixth decl) nil))
    (when (and (not (equal (first lhs) "("))
               (equal (first lhs) "["))
      (let ((b-pos nil)
	    (c-pos nil))
	(setq b-pos (position "]" lhs :test #'equal))
	(setq c-pos (position ":" lhs :test #'equal))
	(when (and b-pos c-pos (= 1 (- c-pos b-pos)))
	  (setf labels (mapcar #'(lambda (x) (intern (string x)))
			       (cdr (firstn lhs b-pos))))
	  (setf lhs (nthcdr (1+ c-pos) lhs)))))
    (%axiom-decl* type labels lhs rhs cond behavioural)))

;;; ********************
;;; LET DECLARATION FORM________________________________________________________
;;; ********************
;;; ("let" "name" "=" ( token .. ))
;;;    0     1     2     3
(defun process-let-declaration-form (toks &rest ignore)
  (declare (ignore ignore))
  (%let* (nth 1 toks) (nth 3 toks)))

;;; **********************
;;; MACRO DECLARATION FORM______________________________________________________
;;; **********************
;;; ("#define" LHS "::=" RHS ".")
;;;      0      1    2    3   4
(defun process-macro-declaration-form (decl &rest ignore)
  (declare (ignore ignore))
  (%macro* (second decl) (fourth decl)))

;;; ***********************
;;; MODULE DECLARATION FORM_____________________________________________________
;;; ***********************
;;;
;;; The parsed token sequence of top level module definition is :
;;; ("mod" <ModName> [ <Parameter> ] [ <PrincipalSort> ] "{" (<Body>) "}")
;;;    0      1              2                3                 4
;;;    0      1              2                                  3
;;;    0      1                               2                 3
;;;    0      1                                                 2
;;;

;;; PROCESS-MODULE-DECLARATION-FORM accepts the token sequence of top level
;;; module declaration form, and convert it to internal representation.
;;; 
(defun process-module-declaration-form (decl &rest ignore)
  (declare (ignore ignore))
  (let* ((mod-type (car decl))          ; kind & type : module, module:sys ...
         (name (nth 1 decl))            ; module name (module expression).
         ;; the following two are optional
         (param nil)                    ; parameter.
         (psort nil)                    ; principal-sort.
         ;; essential part 
         (body  nil)                    ; module body.
         (b-pos 2)                      ; position of beginning of
                                        ; body parts("{") when all of the
                                        ; optional parts are omitted.
         )
    ;; now we accepts 2 optional parts before module body comes:
    (when (consp (nth b-pos decl))      ; supplied param or pricipal-sort
      (incf b-pos)
      (when (consp (nth b-pos decl))    ; supplied both param & principal-sort
        (incf b-pos)))
    ;;
    (case b-pos
      (3                                ; param or principal-sort
       (let ((opt (nth 2 decl)))
         (cond ((member (car opt) '("principal-sort" "psort")
                        :test #'equal)
                (setq psort opt))
               (t (setq param opt)))))
      (4 (setq param (nth 2 decl))
         (setq psort (nth 3 decl))))
    ;;
    (setq body (nth (1+ b-pos) decl))
    (when (atom body) (setq body nil))  ; empty
    ;;
    ;; (format t "~&param=~s" param)
    ;;
    (when param
      (setq param (parse-interface-decl param)))
    ;;
    (when psort
      (setq psort (parse-psort-decl psort)))
    ;;
    (setq mod-type
      (case-equal mod-type
                  (("module" "mod") (cons :module :user))
                  (("sys:mod" "sys:module") (cons :module :system))
                  (("module*" "mod*") (cons :theory :user))
                  (("sys:mod*" "sys:module*") (cons :theory :system))
                  (("module!" "mod!") (cons :object :user))
                  (("sys:mod!" "sys:module!") (cons :object :system))
                  (("hwd:module!" "hwd:mod!") (cons :object :hard))
                  (("ots") (cons :ots :user))
                  (("sys:ots") (cons :ots :system))
                  (("hwd:ots") (cons :ots :hard))
                  (otherwise (error "unsupported type of module ~a" mod-type))))
    ;; parse each module constructs.
    (%module-decl* name
                   (car mod-type)
                   (cdr mod-type)
                   (nconc param
                          psort
                          (parse-module-elements body)))))

;;; PARSE-PSORT-DECL
;;;
(defun parse-psort-decl (decl &rest ignore)
  (declare (ignore ignore))
  (list (%psort-decl* (process-sort-reference-form (cdr decl)))))

;;; PARSE-MODULE-ELEMENTS
;;;  the list of declaration forms are return in order of declaration.
;;;
(defun parse-module-elements (s &rest ignore)
  (declare (ignore ignore))
  (let ((body nil)
	(sig nil)
	(ax nil))
    (dolist (e s)
      (multiple-value-bind (kind elt)
	  (parse-module-element e)
	(case kind
	  (:misc nil)
	  (:sig (setq sig (nconc sig elt)))
	  (:ax (setq ax (nconc ax elt))))))
    (setf body (append sig ax))
    body))

(defun parse-module-element (e &rest ignore)
  (declare (ignore ignore))
  (case-equal (car e)
	      ;; SORT & Subsort Declaration.
              ("bsort" (values :sig (list (process-bsort-declaration e))))
              ("[" (values :sig (process-sort-and-subsort-form e)))
              (("hidden" "*") (values :sig (process-hidden-sort-form e)))

              ;; OPERATOR DECLARATION.
              ("op"
               (values :sig (list (process-operator-declaration-form e))))
              ("ops"
               (values :sig (process-operators-declaration-form e)))
              ("bop"
               (values :sig (list (process-operator-declaration-form e))))
              ("bops"
               (values :sig (process-boperators-declaration-form e)))

              ;; predicate
              ("pred"
               (values :sig (list (process-predicate-declaration-form e))))

              ;; meta-demod predicate
              ("dpred"
               (values :sig (list (process-predicate-declaration-form e))))
              
              ;; behavioural
              ("bpred"
               (values :sig (list (process-predicate-declaration-form e))))
              
              ;; meta-demod behavioural predicate
              ("dbpred"
               (values :sig (list (process-predicate-declaration-form e))))
              
              ;; OPERATOR-ATTRIBUTES.
              (("opattr" "attr" "attrs")
               (values :sig (list (process-opattr-declaration-form e))))
              
              ;; RECORD DECLARATION.
              (("rec" "record")
               (values :sig (list (process-record-declaration-form e))))

              ;; CLASS DECLARATION.
              (("cls" "class")
               (values :sig (list (process-class-declaration-form e))))

              ;; LET Construct. 
              ("let" (values :ax (list (process-let-declaration-form e))))

              ;; Macro
              ("#define" (values :ax (list (process-macro-declaration-form e))))
              
              ;; Axioms
              (("eq" "cq" "ceq" "rule" "rl" "crl" "crule" "trans" "ctrans" "trns" "ctrns"
                     "beq" "bceq" "brule" "brl" "bcrule" "bcrl" "btrans" "btrns"
                     "bctrans" "bctrns")
               (values :ax (list (process-axiom-form e))))

              ;; VARIABLE declaration.
              (("var" "vars")
               (values :ax (list (process-variable-declaration-form e))))
              
              (("pvar" "pvars")
               (values :ax (list (process-pseud-variable-declaration-form e))))
              
              #+:bigpink
              ;; FOPL
              (("fax" "bfax" "ax" "bax" "frm" "bfrm")
               (values :ax (list (pignose-process-fax-proc e))))
              #+:bigpink
              (("goal" "bgoal")
               (values :ax (list (pignose-process-goal-proc e))))
              
              #||
              ("vars-of"                ; NOT YET
               (values :ax (list (process-vars-of-declaration-form e))))
              ||#
              ;; IMPORTATIONS.
              (("imports" "import")
               (let ((body nil)
                     (im-body (caddr e)))
                 (unless (equal im-body "}")
                   (dolist (elt im-body)
                     (unless (equal im-body "}")
                       (case-equal (car elt)
                                   (("--" "**") nil)
                                   ("-->" (setq body (nconc body
                                                            (list (%dyna-comment*
                                                                   (cons "--" (cdr elt)))))))
                                   ("**>" (setq body
                                            (nconc body (list
                                                         (%dyna-comment* (cons "**" (cdr elt)))))))
                                   (t (setf body (nconc body (process-importation-form elt))))))))
                 (values :sig body)))
              
              (("pr" "protecting" "ex" "extending" "us" "using" "inc" "including")
               (values :sig (process-importation-form e)))

              ;; Comments.
              ;; must prepare ....
              (("--" "**") (values :misc nil)) ; do nothing
              ;; should delay the output.
              ("-->" (let ((comm (%dyna-comment* (cons "--" (cdr e)))))
		       (eval-ast comm)
		       (values :misc nil)))
              ("**>" (let ((comm (%dyna-comment* (cons "**" (cdr e)))))
		       (eval-ast comm)
		       (values :misc nil)))

              ;; AS -- not yet
              ;; ("as" (list (process-as-form e)))
              ;; OP-AS -- not yet
              ;; ("op-as" (list (process-op-as-form e)))

              ;; MISC .. 
              (("ev" "lisp" "evq" "lispq")
	       (let ((form (%lisp-eval* (cadr e))))
		 (eval-ast form)
		 (values :misc nil)))

              (("eval")
               (list (values :misc (%eval* (cadr e)))))
              
              ;; SIG, AX
              (("sig" "signature")
               (let ((body nil)
                     (s-body (caddr e)))
                 (unless (equal s-body "}")
                   (dolist (elt s-body)
                     (unless (equal elt "}")
		       (multiple-value-bind (type sig)
			   (parse-module-element elt)
			 (declare (ignore type))
			 (setf body (nconc body sig))))))
                 (values :sig body)))
              
              (("axioms" "axiom" "axs")
               (let ((body nil)
                     (a-body (caddr e)))
                 (unless (equal a-body "}")
                   (dolist (elt a-body)
                     (unless (equal elt "}" )
		       (multiple-value-bind (type ax)
			   (parse-module-element elt)
			 (declare (ignore type))
                       (setf body (nconc body ax))))))
                 (values :sig body)))

              ((".")                    ; sole dots
               (values :misc nil))
              ;; Unknown...
              (t (format t "~&Processing module elements : unknown form: ~a, ignored." e)
                 (values :misc nil))))

(defun parse-module-element-1 (e &rest ignore)
  (multiple-value-bind (type elt)
      (parse-module-element e ignore)
    (declare (ignore type))
    (car elt)))

;;; ********************
;;; VIEW DECLARTION FORM _______________________________________________________
;;; ********************

(defun process-view-declaration-form (defn &rest ignore)
  (declare (ignore ignore))
  (let ((view-name (second defn))
        (view-frag (caddr defn)))
    (let ((view-form
           (if (equal "of" (car view-frag))
               ` ("view" "from" ,(nth 3 view-frag)
                         "to" ,(nth 1 view-frag)
                         ,@(cddddr view-frag)
                         "}")
             ` ("view" ,@view-frag "}"))))
      (let ((vwpars (parse-view view-form)))
        (%view-decl* view-name vwpars)))))

;;; EOF
