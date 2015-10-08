;;;-*-Mode:LISP; Package: CHAOS; Base:10; Syntax:Common-lisp -*-
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
(in-package :chaos)
#|=============================================================================
                                  System:CHAOS
                                Module:construct
                               File:gen-rule.lisp
=============================================================================|#
#-:chaos-debug
(declaim (optimize (speed 3) (safety 0) #-GCL (debug 0)))
#+:chaos-debug
(declaim (optimize (speed 1) (safety 3) #-GCL (debug 3)))

;;; GENERATE REWRITE RULES module : -> module'
;;;-----------------------------------------------------------------------------
;;;
(defun generate-rewrite-rules (module)
  (declare (type module module)
           (values t))
  (compute-protected-modules module)

  ;; install own rules.
  (let ((axiom-set (module-axiom-set module)))
    (dolist (eq (axiom-set$equations axiom-set))
      (gen-rule-internal eq module))
    (dolist (rule (axiom-set$rules axiom-set))
      (gen-rule-internal rule module)))

  ;; specialize rules of sumodules.
  (dolist (rule (gather-submodule-rules module))
    (let ((r-rule (or (cdr (assq rule (module-axioms-to-be-fixed module)))
                      rule)))
      (unless (memq (axiom-type r-rule) '(:pignose-axiom :pignose-goal))
        (specialize-rule r-rule module))))
  module)

(defun variable-occurs-in (t1 t2)
  (declare (type term t1 t2))
  (or (term-is-identical t1 t2)
      (and (term-is-application-form? t2)
           (dolist (sub (term-subterms t2) nil)
             (when (variable-occurs-in t1 sub)
               (return-from variable-occurs-in t))))))

(defparameter non-exec-labels '(|:nonexec| |:non-exec| |:no-ex| |:noex| |:noexec|))

(defun axiom-is-non-exec? (ax)
  (intersection (axiom-labels ax) non-exec-labels))

(defun condition-has-match-condition (condition)
  (and condition
       (member *bool-match* (term-methods condition))))
  
(defun gen-rule-internal (ax module &aux (rule ax))
  (declare (type axiom ax)
           (type module module)
           (type axiom rule)
           (values t))
  (when (memq (axiom-type ax) '(:pignose-axiom :pignose-goal))
    (return-from gen-rule-internal nil))
  ;;
  (setq rule (or (cdr (assq ax (module-axioms-to-be-fixed module)))
                 ax))
  ;;
  (when (axiom-is-non-exec? ax)
    (setf (axiom-non-exec ax) t)
    (setf (rule-non-exec rule) t))
  ;;
  (let ((lhsv (term-variables (axiom-lhs rule))))
    (declare (type list lhsv))
    ;; for trans sole variable on LHS is allowed
    (when (term-is-variable? (axiom-lhs rule))
      (when (variable-occurs-in (axiom-lhs rule)
                                (axiom-rhs rule))
        (setf (axiom-need-copy rule) t))
      (unless (eq (axiom-type rule) :rule)
        (unless (axiom-non-exec rule)
          (with-output-chaos-warning ()
            (princ "the LHS of axiom : ")
            (print-next)
            (print-chaos-object rule)
            (print-next)
            (princ "   is just a variable, ignored as rewrite rule.")))
        (setf (axiom-kind rule) ':bad-rule)
        (setf (axiom-kind ax) ':bad-rule))
      (return-from gen-rule-internal nil))
    (let ((rhs-vars (term-variables (axiom-rhs rule)))
          (cond-vars (term-variables (axiom-condition rule))))
      (declare (type list rhs-vars cond-vars))
      (cond ((and lhsv
                  (or (not (subsetp rhs-vars lhsv))
                      (not (subsetp cond-vars lhsv))))
             (unless (or (term-contains-match-op (axiom-rhs rule))
                         (term-contains-match-op (axiom-condition rule)))
               (when *chaos-verbose*
                 (with-output-chaos-warning ()
                   (format t "RHS of the axiom has extra variable(s) which does not occur in LHS.")
                   (print-next)
                   (print-axiom-brief rule))))
             (add-rule-to-module module rule)
             (unless (term-is-variable? (axiom-lhs rule))
               (add-associative-extensions module
                                           (term-head (axiom-lhs rule))
                                           rule)
               (specialize-rule rule module)))
            ((and (axiom-is-behavioural rule)
                  (not (and (term-can-be-in-beh-axiom? (axiom-lhs rule))
                            (term-can-be-in-beh-axiom? (axiom-rhs rule)))))
             (when *chaos-verbose*
               (with-output-chaos-warning ()
                 (princ "axiom violates context condition of behavioural axiom")
                 (print-next)
                 (print-chaos-object rule)))
             (if *allow-illegal-beh-axiom*
                 (progn
                   (setf (axiom-kind rule) ':bad-beh)
                   (setf (axiom-kind ax) ':bad-beh)
                   (add-rule-to-module module rule)
                   (add-associative-extensions module
                                               (term-head (axiom-lhs rule))
                                               rule)
                   (specialize-rule rule module))
                 (progn
                   (setf (axiom-kind rule) ':bad-rule)
                   (setf (axiom-kind ax) ':bad-rule))))
            ;; all is ok, we can use this axiom as a rewrite rule
            (t (add-rule-to-module module rule)
               (unless (term-is-variable? (axiom-lhs rule))
                 (add-associative-extensions module
                                             (term-head (axiom-lhs rule))
                                             rule)
                 (specialize-rule rule module)))))))

(defun gather-submodule-rules (module)
  (declare (type module module)
           (values list))
  (labels ((module-specific-rules (mod)
             (let ((res nil))
               (dolist (e (module-own-axioms mod) res)
                 #||
                 (let ((new (cdr (assq e (module-axioms-to-be-fixed mod)))))
                   (when new (setq e new))
                   (unless (term-is-variable? (axiom-lhs e))
                     (push e res)))
                 ||#
                 (block next-axiom
                   (let ((lhs (rule-lhs e)))
                     (when (and (term-is-applform? lhs)
                                (method-is-error-method (term-head lhs)))
                       (return-from next-axiom nil))
                     (unless (term-is-variable? lhs)
                       (push e res))))
                 )))
           (rule-member? (rule list-of-rule)
             (dolist (e list-of-rule)
               (when (rule-is-similar? rule e)
                 (return t))))
           (union-rules (ax1 ax2)
             (let ((res ax2))
               (dolist (ex ax1)
                 (unless (rule-member? ex res) (push ex res)))
               res) ))
    (let ((res nil))
      (dolist (submodule (module-all-submodules module))
        (unless (or (eq :using (cdr submodule))
                    (eq :modmorph (cdr submodule)))
          (unless (module-is-ready-for-rewriting (car submodule))
            (compile-module (car submodule)))
          (setf res (union-rules (module-specific-rules (car submodule)) res))))
      res)))

(defun get-dis-submodule-axioms (mod)
  (declare (type module mod)
           (values list))
  (let ((res nil))
    (dolist (submodule (module-all-submodules mod))
      (unless (or (eq :using (cdr submodule))
                  (eq :modmorph (cdr submodule)))
        (unless (module-is-ready-for-rewriting (car submodule))
          (compile-module (car submodule)))
        (push (cons (car submodule)
                    (module-own-axioms (car submodule)))
              res)))
    res))

;;; TODO for record/class.
;;;
(defvar *ignore-protected-modules* nil)

(defun specialize-rule (r mod)
  (declare (type axiom r)
           (type module mod)
           (values t))
  (let* ((lhs (axiom-lhs r))
         (method (if (term-is-applform? lhs)
                     (term-head lhs)
                     nil))
         (mmod (method-module method))
         (promod (if *ignore-protected-modules*
                     nil
                     (module-protected-modules mod)))
         (opinfo-table (module-opinfo-table mod)))
    (when (and method
               (null (get-method-info method (module-opinfo-table mod))))
      (return-from specialize-rule nil))
    ;;
    (when (and method (method-is-error-method method))
      ;; we must add this rule to module.
      (setq r (recreate-error-axiom r mod))
      (add-rule-to-method r method (module-opinfo-table mod)))
    ;;
    (unless (term-is-variable? lhs)
      (specialize-for-methods
       r 
       (if (method-is-universal method)
           (method-lower-methods method opinfo-table)
           (remove-if #'(lambda (meth)
                          (let ((xmod (method-module meth)))
                            (and (not (eq xmod mmod))
                                 (if (assq mmod (module-all-submodules xmod))
                                     (memq mmod (module-protected-modules xmod))
                                     (memq xmod promod)))))
                      (method-lower-methods method opinfo-table)))
       mod))))

(defun specialize-for-methods (r methods mod)
  (declare (type axiom r)
           (type list methods)
           (type module mod)
           (values t))
  (let ((lhs (axiom-lhs r)))
    (dolist (method methods)
      (when (rule-check-down mod method (term-subterms lhs))
        (add-rule-to-method r method (module-opinfo-table mod))
        (add-associative-extensions mod method r)
        ))
    (add-associative-extensions mod (term-head lhs) r)
    mod))

(defun add-associative-extensions (mod method r)
  (declare (type module mod)
           (type method method)
           (type axiom r)
           (values t))
  (when (term-is-lisp-form? (rule-rhs r))
    (return-from add-associative-extensions nil))
  (when (method-is-associative method)
    (dolist (method-above (list-associative-method-above method))
      (unless (or (method-is-error-method method-above)
                  (member r (method-all-rules method-above)))
        (if (method-is-commutative method-above)
            ;; AC extension
            (let ((new-var (make-variable-term (car (method-arity method-above))
                                               ;; *cosmos*
                                               'ac))
                  ac-rule)
              (setf ac-rule
                    (make-rule
                     :lhs (make-right-assoc-normal-form method-above
                                                        (cons new-var
                                                              (list-assoc-subterms
                                                               (axiom-lhs r)
                                                               (term-head
                                                                (axiom-lhs r)))))
                     :rhs (make-applform (method-coarity method-above)
                                         method-above
                                         (list new-var
                                               ;;(substitution-check-builtin
                                               ;;  (axiom-rhs r))
                                               (axiom-rhs r)
                                               ))
                     :condition (axiom-condition r)
                     :id-condition (axiom-id-condition r)
                     :labels (axiom-labels r)
                     :type (axiom-type r)
                     :meta-and-or (rule-meta-and-or r)
                     :behavioural (axiom-is-behavioural r)
                     :kind (if (eq ':id-theorem (axiom-kind r))
                               ':id-ext-theory
                               ':ac-theory)))
              ;; (compute-rule-method ac-rule)
              (add-rule-to-method ac-rule method-above (module-opinfo-table mod)))
                                                              
            ;; A extension.
            (let ((new-var (make-variable-term *cosmos* 'a1))
                  (new-var2 (make-variable-term *cosmos* 'a2))
                  a-rule)
              (setf a-rule
                    (make-rule
                     :lhs (make-right-assoc-normal-form method-above
                                                        (cons new-var
                                                              (list-assoc-subterms
                                                               (axiom-lhs r)
                                                               (term-head
                                                                (axiom-lhs r)))))
                     :rhs (make-applform (method-coarity method-above)
                                         method-above
                                         (list new-var
                                               ;;(substitution-check-builtin
                                               ;;(axiom-rhs r))
                                               (axiom-rhs r)
                                               ))
                     :condition (axiom-condition r)
                     :id-condition (axiom-id-condition r)
                     :labels (axiom-labels r)
                     :type (axiom-type r)
                     :meta-and-or (rule-meta-and-or r)
                     :behavioural (axiom-is-behavioural r)
                     :kind (if (eq ':id-theorem (axiom-kind r))
                               ':id-ext-theory
                               ':a-left-theory)))
              ;; (compute-rule-method a-rule)
              (add-rule-to-method a-rule method-above (module-opinfo-table mod))

              (setf a-rule
                    (make-rule
                     :lhs (make-right-assoc-normal-form method-above    
                                                        (append
                                                         (list-assoc-subterms
                                                          (axiom-lhs r)
                                                          (term-head (axiom-lhs r)))
                                                         (list new-var)))
                     :rhs (make-applform (method-coarity method-above)
                                         method-above
                                         (list ;; (substitution-check-builtin (axiom-rhs r))
                                               (axiom-rhs r)
                                               new-var))
                     :condition (axiom-condition r)
                     :id-condition (axiom-id-condition r)
                     :labels (axiom-labels r)
                     :type (axiom-type r)
                     :meta-and-or (rule-meta-and-or r)
                     :behavioural (axiom-is-behavioural r)
                     :kind (if (eq ':id-theorem (axiom-kind r))
                               ':id-ext-theory
                               ':a-right-theory)))
              (add-rule-to-method a-rule method-above (module-opinfo-table mod))
              
              (setf a-rule
                    (make-rule
                     :lhs (make-right-assoc-normal-form method-above
                                                        (append (list new-var2)
                                                                (list-assoc-subterms
                                                                 (axiom-lhs r)
                                                                 (term-head
                                                                  (axiom-lhs
                                                                   r))) 
                                                                (list new-var)))
                     :rhs (make-right-assoc-normal-form
                           method-above
                           (list new-var2
                                 ;; (substitution-check-built-in (axiom-rhs r))
                                 (axiom-rhs r)
                                 new-var))
                     :condition (axiom-condition r)
                     :id-condition (axiom-id-condition r)
                     :labels (axiom-labels r)
                     :type (axiom-type r)
                     :meta-and-or (rule-meta-and-or r)
                     :behavioural (axiom-is-behavioural r)
                     :kind (if (eq ':id-theorem (axiom-kind r))
                               ':id-ext-theory
                               ':a-middle-theory)))
              (add-rule-to-method a-rule method-above (module-opinfo-table mod))))))))

(defun rule-check-down (mod method terms)
  (declare (ignore mod)
           (type module mod)
           (type method method)
           (type list terms)
           (values (or null t)))
  (not (eq ':fail
           (compute-var-info
            (mapcar #'cons terms (method-arity method))
            nil))))

;; term-s ::= ( (term . sort) ... )
;; cvi    ::= ( (variable . (sort ... )) ... )
;;
(defun sort-is-general (sort)
  (declare (type sort-struct sort)
           (values (or null t)))
  (or (sort= sort *cosmos*)
      (sort= sort *universal-sort*)
      (sort= sort *huniversal-sort*)))

(defun compute-var-info (term-s cvi)
  (declare (type list term-s cvi)
           (values t))
  (if (null term-s)
      cvi
      (let ((term (caar term-s))
            (sort (cdar term-s)))
        (declare (type term term)
                 (type sort* sort))
        (cond ((term-is-variable? term)
               (let ((vi (cdr (assoc term cvi))))
                 (if vi
                     (if (member sort vi)
                         (compute-var-info (cdr term-s) cvi)
                         (let ((res (if (sort-is-general sort)
                                        (list sort)
                                        (max-minorants (cons sort vi)
                                                       *current-sort-order*))))
                           (if res
                               (compute-var-info
                                (cdr term-s) (cons (cons term res) cvi))
                               ;; don't really need to add new if res = [sort set] vi
                               ':fail)))
                     (let ((vs (variable-sort term)))
                       (if (sort= vs sort)
                           (compute-var-info
                            (cdr term-s) (cons (cons term (list sort)) cvi))
                           (let ((res (if (sort-is-general vs)
                                          (list sort)
                                          (max-minorants (list sort vs)
                                                         *current-sort-order*))))
                             (if res
                                 (compute-var-info
                                  (cdr term-s) (cons (cons term res) cvi))
                                 ':fail)))))))
              ((term-is-builtin-constant? term)
               (if (sort<= (term-sort term) sort *current-sort-order*)
                   (compute-var-info (cdr term-s) cvi)
                   ':fail))
              (t (let ((methods (highest-methods-below (term-head term) sort)))
                   (if (null methods)
                       ':fail
                       (dolist (meth methods ':fail)
                         (let ((res (compute-var-info
                                     (append (mapcar #'cons
                                                     (term-subterms term)   
                                                     (method-arity meth)) 
                                             (cdr term-s)) 
                                     cvi)))
                           (unless (eq ':fail res)
                             (return res)))))))))))

;;;-----------------------------------------------------------------------------
(defun normalize-rules-in (mod)
  mod)

;;;=============================================================================
;;;               SPECIAL AXIOMS FOR IDEMPOTENT & IDENTITY
;;;_____________________________________________________________________________

(let (($rule-counter 0))
  (declare (type fixnum $rule-counter))
  
  (defun create-rule-name (mod label)
    (declare (ignore mod)
             (type simple-string label)
             (values list))
    (prog1
        (list (intern (format nil "~a~a" label $rule-counter)))
      (incf $rule-counter))))

(defun add-operator-theory-axioms (module opinfo)
  (declare (type module module)
           (type list opinfo)
           (values t))
  (let* ((op (opinfo-operator opinfo))
         thy
         (var nil)
         (l-sort nil)
         (var2 nil)
         (r-sort nil))
    (dolist (meth (opinfo-methods opinfo))
      (when (and (eq (method-module meth) module)
                 (not (method-is-error-method meth)))
        (setf thy (method-theory meth))
        ;; IDEM
        (when (theory-contains-idempotency thy)
          (setq l-sort (car (method-arity meth)))
          (setq var (make-variable-term l-sort '|U-idem|))
          (adjoin-axiom-to-module
           module
           (make-rule
            :lhs (make-applform (method-coarity meth)
                                meth
                                (list var var))
            :rhs var
            :condition *BOOL-TRUE*
            :labels (create-rule-name module "idem")
            :type ':equation
            :kind ':IDEM-THEORY)))
        ;; IDENT
        (when (and (or (theory-contains-identity thy) (theory-zero thy))
                   (= 2 (the fixnum (operator-num-args op))))
          (let* ((so (module-sort-order module))
                 (comm (theory-contains-commutativity thy))
                 (id (car (theory-zero thy)))
                 (id-sort (cond ((term-is-builtin-constant? id)
                                 (term-sort id))
                                ((term-is-applform? id)
                                 (method-coarity (term-head id)))
                                (t (error "Internal Error, Illegal identity ~s" id)))))
            (setq l-sort (car (method-arity meth)))
            (setq r-sort (cadr (method-arity meth)))
            (let ((flag nil))
              (when id
                ;; add axiom: id op x = x
                (when (sort<= id-sort l-sort so)
                  (setq flag t)
                  (setq var (make-variable-term l-sort 'X-id))
                  (adjoin-axiom-to-module
                   module
                   (make-rule
                    :lhs (make-applform (method-coarity meth)
                                        meth
                                        (list id var))
                    :rhs var
                    :condition *BOOL-TRUE*
                    :type ':equation
                    :labels (create-rule-name module "ident")
                    :kind ':ID-THEOREM)))
                ;; add axiom: x op id = x (possibly).
                (unless (and flag comm)
                  (when (sort<= id-sort r-sort so)
                    (setq var2 (make-variable-term l-sort 'Y-id))
                    (adjoin-axiom-to-module
                     module
                     (make-rule
                      :lhs (make-applform (method-coarity meth)
                                          meth
                                          (list var2 id))
                      :rhs var2
                      :condition *BOOL-TRUE*
                      :labels (create-rule-name module "ident")
                      :type ':equation
                      :kind ':ID-THEOREM))))))))))))

(defun add-identity-completions (module)
  (declare (type module module)
           (values t))
  (when *no-id-completion*
    (return-from add-identity-completions nil))
  (with-in-module (module)
    (when (some #'(lambda (opinfo)
                    (dolist (meth (opinfo-methods opinfo))
                      (let ((thy (method-theory meth)))
                        (when (and (theory-contains-identity thy)
                                   (not (cdr (theory-zero thy))))
                          (return t)))))
                (module-all-operators module))
      (dolist (a (axiom-set$equations (module-axiom-set module)))
        (add-identity-completions-internal a module))
      (dolist (r (axiom-set$rules (module-axiom-set module)))
        (add-identity-completions-internal r module)))))

(defun add-identity-completions-internal (r module)
  (declare (type axiom r)
           (type module module)
           (values t))
  (when *gen-rule-debug*
    (format t "~%[id-compl] given rule ~a, of kind ~a " r (axiom-kind r))
    (print-next))
  (unless (axiom-kind r)
    (let (varval
          (res nil)
          (newres (list (list r nil nil)))
          a-axiom
          subst
          val)
      (loop
         (setq val (car newres))
         (setq newres (cdr newres))
         (setq a-axiom (car val))
         (setq subst (cadr val))
         ;; -- res    : LIST[rule subst [status]].
         ;; -- varval : value to substitute in,
         ;; -- a-axiom: rule generating new axioms from
         ;; -- status : bad/good --- in res have status, but not in newres
         (if (test-bad-axiom a-axiom)
             (unless (rule-inf-subst-member subst res)
               (setq res (cons (list a-axiom subst 'bad) res)))
             (progn
               (setq res (cons (list a-axiom subst 'good) res))
               (let ((donesubst nil)
                     sub1
                     new-axiom
                     newsubst)
                 (loop
                    (setq varval
                          (compute-var-for-identity-completions
                           (axiom-lhs a-axiom)
                           donesubst))
                    (unless varval (return))
                    (setq sub1 (cons varval nil))
                    (setq newsubst (substitution-can (cons varval subst)))
                    (setq donesubst (cons (car sub1) donesubst))
                    (setq new-axiom (insert-val sub1 a-axiom module))
                    (unless (or (null new-axiom)
                                (rule-inf-subst-member newsubst res))
                      (setq newres (cons (list new-axiom newsubst) newres)))))))
         (unless newres (return)))
      ;;
      (let ((errs nil)
            (rules1 nil)
            (rules2 nil)
            badver)
        (dolist (ruli res)
          (let ((rul (car ruli)))
            (if (eq 'bad (nth 2 ruli))
                (push ruli errs)
                (unless (rule-inf-member rul rules1)
                  (push ruli rules1)))))
        ;;
        (setq rules2 (list (list r nil)))
        (dolist (ruli rules1)
          (let ((rul (car ruli)))
            (unless (or (dolist (ruli2 rules2 nil)
                          (when (rule-subsumes (car ruli2) rul)
                            (return t)))
                        (dolist (ruli2 rules1 nil)
                          (let ((rul2 (car ruli2)))
                            (when (and (not (eq rul rul2))
                                       (rule-strictly-subsumes rul2 rul))
                              (return t)))))
              (push ruli rules2))))
        ;;
        (when *chaos-verbose*
          (let ((rs (reverse rules1)))
            (format t "~%** id-completion for rule: ")
            (print-axiom-brief r)
            (let ((*print-indent* (+ 2 *print-indent*)))
              (print-next)
              (princ "-- Generated rules:")
              (print-next)
              (if rs
                  (let ((*chaos-verbose* nil))
                    (dolist (r (reverse rs))
                      (print-axiom-brief (car r))
                      (print-next)))
                  (progn (princ "none") (print-next)))
              (princ "-- Generated, but invalid rules:")
              (print-next)
              (if errs
                  (let ((lst (reverse errs)))
                    (loop
                       (when (null lst) (return))
                       (unless (rule-inf-member (caar lst) (cdr lst))
                         (print-axiom-brief (caar lst))
                         (print-next))
                       (setq lst (cdr lst))))
                (progn (princ "none") (print-next)))))
          (flush-all))
        ;;
        (dolist (ruli rules2)
          (let ((rul (car ruli))
                (rulsubst (cadr ruli)))
            (setq badver nil)
            (dolist (bruli errs)
              (when (substitution-subset-list rulsubst (cadr bruli))
                (push (cadr bruli) badver)))
            (let ((newrule rul)
                  (newidcond (make-id-condition (term-variables (axiom-lhs rul))
                                                badver)))
              (when *chaos-verbose*
                (unless (and (null newidcond) (eq r newrule))
                  (if (eq r newrule)
                      (format t "~%  -- Modified with Id condition:~%  ")
                      (if (rule-occurs newrule (module-equations module))
                          (format t "~%  -- Required rule: ~%  ")
                        (format t "~%  -- Added rule: ~%  "))))
                (flush-all))
              ;;
              (setf (axiom-id-condition newrule) newidcond)
              (when (and (null (axiom-labels newrule))
                         (not (eq r newrule)))
                (setf (axiom-labels newrule)
                      (create-rule-name module "compl")))
              (when (axiom-extensions newrule)
                (dolist (e (axiom-a-extensions newrule)) 
                  (setf (axiom-id-condition e) newidcond))
                (dolist (e (axiom-AC-extension newrule))
                  (setf (axiom-id-condition e) newidcond)))
              (dolist (e (axiom-extensions newrule))
                (when e
                  (setf (axiom-id-condition e) newidcond)))
              ;;
              (when *chaos-verbose*
                (unless (and (null newidcond) (eq r rul))
                  (print-axiom-brief rul)))
              ;;
              (unless (eq r rul)
                (when *gen-rule-debug*
                  (format t "~%[id-compl]=> ")
                  (print-chaos-object newrule))
                (adjoin-axiom-to-module module newrule)))))))))

;;; mark rules which brings problematic rewrting (LHS is var, infinite loop) as 'bad
;;;
(defun test-bad-axiom (ax)
  (declare (type axiom ax)
           (values (or null t)))
  (or (term-is-variable? (axiom-lhs ax))
      (and (is-true? (axiom-condition ax))
           (term-occurs-as-subterm (axiom-lhs ax) (axiom-rhs ax)))
      (term-occurs-as-subterm (axiom-lhs ax) (axiom-condition ax))
      (term-is-similar? (axiom-lhs ax) (axiom-rhs ax))))

(defun rule-inf-member (ax riset)
  (declare (type axiom ax)
           (type list riset)
           (values (or null t)))
  (dolist (ax2 riset nil)
    (when (rule-is-similar? ax (car ax2))
      (return t))))

(defun rule-inf-subst-member (subst riset)
  (declare (type list subst riset)
           (values (or null t)))
  (dolist (rul2 riset nil)
    (when (substitution-equal subst (cadr rul2))
      (return t))))

;;; t1 is not a variable.
;;; Should really deal with some sort of evaluation strategy issues
;;; but we are in a bind, since we don't know them at "this point".
(defun term-occurs-as-subterm (t1 t2)
  (declare (type term t1 t2)
           (values (or null t)))
  (when *gen-rule-debug*
    (with-output-simple-msg ()
      (format t "[term-occurs-as-subterm]: t1 = ")
      (print-chaos-object t1)
      (print-next)
      (format t "-- t2 = ")
      (print-chaos-object t2)))
  (if (term-is-variable? t2)
      nil
      (if (term-is-applform? t2)
          (multiple-value-bind (gst subs nomatch eequal)
              (if (method-is-of-same-operator (term-head t1) (term-head t2))
                  (first-match t1 t2)
                  (values nil nil t nil))
            (declare (ignore gst subs eequal))
            (if (not nomatch)
                t
                (dolist (t2st (term-subterms t2) nil)
                  (when (term-occurs-as-subterm t1 t2st) (return t)))))
          ;;
          nil)))

(defun compute-var-for-identity-completions (term donesubst)
  (declare (type term term)
           (type list donesubst))
  (select-var-for-identity-completions term donesubst))

(defun select-var-for-identity-completions (term donesubst)
  (declare (type term term)
           (type list donesubst))
  (cond ((or (term-is-variable? term) (term-is-constant? term)) nil)
        (t (let* ((meth (term-head term))
                  (thy (method-theory meth))
                  (id-flag (and (theory-contains-identity thy)
                                (null (cdr (theory-zero thy)))))
                  (id (if id-flag (car (theory-zero thy)))))
             (if id
                 (select-var-for-identity-completions-alt2 meth id term donesubst)
               (dolist (sb (term-subterms term))
                 (let ((val (select-var-for-identity-completions sb donesubst)))
                   (when val (return val)))))))))

(defun select-var-for-identity-completions-alt2 (meth id term donesubst)
  (declare (type method meth)
           (type t id)
           (type term term)
           (type list donesubst))
  (let ((val1 (select-var-for-identity-completions-alt meth
                                                       id
                                                       (term-arg-1 term)
                                                       donesubst)))
    (if val1
        val1
      (let ((val2 (select-var-for-identity-completions-alt meth
                                                           id
                                                           (term-arg-2 term)
                                                           donesubst)))
        val2))))

(defun select-var-for-identity-completions-alt (meth id term donesubst)
  (declare (type method meth)
           (type t id)
           (type term term)
           (type list donesubst))
  (cond ((term-is-variable? term)
         (let ((srt (variable-sort term))
               (so (module-sort-order *current-module*)))
           (when (and (not (term-is-an-error id))
                      (sort<= (term-sort id) srt so)
                      (not (occurs-var-val term id donesubst)))
             (cons term id))))
        ((term-is-constant? term) nil)
        ((method= meth (term-head term))
         (select-var-for-identity-completions-alt2 meth id term donesubst))
        ((theory-is-empty-for-matching (method-theory (term-head term)))
         (select-var-for-identity-completions term donesubst))
        (t (select-var-for-identity-completions term donesubst))))

(defun occurs-var-val (var val y)
  (declare (type term var val)
           (type list y)
           (values (or null t)))
  (dolist (ye y nil)
    (when (and (eq var (car ye))
               (eq val (cdr ye)))
      (return t))))

(defun insert-val (subs rul &optional (module *current-module*))
  (declare (type list subs)
           (type axiom rul)
           (values (or null axiom)))
  (let (($$trace-rewrite nil)
        ($$trace-rewrite-whole nil)
        (*m-pattern-subst* nil))
    (let ((newcond (if (is-true? (axiom-condition rul))
                       *BOOL-true*
                       (term-simplify
                        (normalize-for-identity-total
                         (substitution-partial-image subs (axiom-condition rul)))
                        module))))
      (when *gen-rule-debug*
        (format t "~%[insert-val]:----------")
        (format t "~% given rule : ")
        (print-axiom-brief rul)
        (format t "~% subst : ")
        (print-substitution subs)
        (format t "~% newcond : ")
        (term-print-with-sort newcond))
      (if (is-false? newcond)
          (progn
            (when *gen-rule-debug*
              (format t "~%  newcond = ")
              (term-print-with-sort newcond))
            nil)
          (let ((rule nil)
                (lhs (normalize-for-identity-total
                      (substitution-partial-image subs (axiom-lhs rul))))
                (rhs (term-simplify
                      (normalize-for-identity-total
                       (substitution-partial-image subs
                                                   (axiom-rhs rul)))
                      module))
                (condition (if (is-true? newcond)
                               *BOOL-TRUE*
                               newcond)))
            (unless (and (term-is-really-well-defined lhs)
                         (term-is-really-well-defined rhs)
                         (term-is-really-well-defined condition))
              (when *gen-rule-debug*
                (format t "~%<< ill defined axiom: ")
                (format t "~% lhs: ")(term-print-with-sort lhs)
                (format t "~% rhs: ")(term-print-with-sort rhs)
                (format t "~% cnd: ")(term-print-with-sort condition))
              (return-from insert-val nil))
            (setq rule
                  (make-rule
                   :lhs lhs
                   :rhs rhs
                   :condition condition
                   :type (axiom-type rul)
                   :kind ':id-completion
                   :meta-and-or (rule-meta-and-or rul)
                   :labels (cons (car (create-rule-name 'dummy "idcomp")) (axiom-labels rul))))
            ;;
            (when *gen-rule-debug*
              (format t "~% gen rule : ")
              (print-chaos-object rule))
            rule)))))
  
;;;=============================================================================
(defun rule-make-or-list (l)
  (declare (type list l)
           (values list))
  (if (null (cdr l)) (car l) (cons 'or l)))

(defun rule-make-and-list (l)
  (declare (type list l)
           (values list))
  (if (null (cdr l)) (car l) (cons 'and l)))

(defun rule-make-eqeqeq (x)
  (declare (type list x)
           (values list))
  (list 'equal (car x) (cdr x)))

(defun rule-make-or-cond (x y)
  (declare (type list x y)
           (values list))
  (if (eq nil y) x
      (if (and (consp y) (eq 'or (car y)))
          (list* 'or x (cdr y))
          (list 'or x y))))

(defun rule-make-and-cond (x y)
  (declare (type t x y)
           (values list))
  (if (eq 't y) x
      (if (and (consp y) (eq 'and (car y)))
          (list* 'and x (cdr y))
          (list 'and x y))))

(defvar *enable-id-condition* t)

(defun make-id-condition (vars subs)
  (declare (type list vars subs)
           (values list))
  (when *enable-id-condition* 
    (let ((subs2 nil))
      (dolist (sub subs)
        (when sub
          (let ((subcan (substitution-can (substitution-restrict vars sub))))
            (unless (or (null subcan)
                        (member subcan subs2 :test #'substitution-equal))
              (push subcan subs2)))))
      (when subs2
        (list 'not (make-improved-id-cond subs2))))))

;;; cond as list of substitutions
(defun make-improved-id-cond (cond)
  (declare (type (or null term) cond))
  (if cond
      (let ((atomic (compute-atomic cond)))
        (improve-id-cnd (elim-supersets (canonicalize-atomic cond atomic))))
    nil))

;;; c assumed canonicalized and in DNF
;;; result is and/or/equal expression
(defun improve-id-cnd (c)
  (declare (type list c))
  (if (null (cdr c))
      (rule-make-and-list
       (mapcar #'rule-make-eqeqeq (car c)))
    (let ((freqs (compute-atomic-freq c))
          max
          nxt
          p1
          p2
          flag)
      (declare (type (or null fixnum) max))
      ;;
      (setq nxt (caar freqs))
      (setq max (cdar freqs))
      (dolist (e (cdr freqs))
        (when (< (the fixnum max) (the fixnum (cdr e)))
          (setq nxt (car e)  max (cdr e))))
      (setq p1 nil  p2 nil  flag t)
      (dolist (s c)
        (unless (null s)
          (if (member-atomic nxt s)
              (when flag
                (let ((res (remove-atomic nxt s)))
                  (if (null res)
                      (setq flag nil
                            p1 nil)
                    (push res p1))))
            (push s p2))))
      (when (and p1 (null flag)) (break "ERR"))
      (if p1
          (setq p1 (improve-id-cnd p1))
        (setq p1 t))
      (when p2 (setq p2 (improve-id-cnd p2)))
      (rule-make-or-cond (rule-make-and-cond (rule-make-eqeqeq nxt) p1)
                         p2))))

;;; arg is list of substs
(defun compute-atomic (expr)
  (declare (type list expr))
  (let ((res nil))
    (dolist (x expr)
      (dolist (y x)
        (unless (member-atomic y res)
          (push y res))))
    res))

;;; arg is list of substs
(defun canonicalize-atomic (e atoms)
  (declare (type list e atoms)
           (values list))
  (mapcar #'(lambda (x)
              (mapcar #'(lambda (y)
                          (or (member-atomic y atoms)
                              y))
                      x))
          e))

(defun compute-atomic-freq (expr)
  (declare (type list expr)
           (values list))
  (let ((res nil))
    (dolist (x expr)
      (dolist (y x)
        (let ((val (assoc-atomic y res)))
          (if val (incf (the fixnum (cdr val)))
              (push (cons y 1) res)))))
    res))

(defun member-atomic (x lst)
  (declare (type list lst)
           (type t x)
           (values (or null t)))
  (dolist (e lst nil)
    (when (same-atomic x e) (return e))))

(defun remove-atomic (x lst)
  (declare (type t x)
           (type list lst)
           (values list))
  (let ((res nil))
    (dolist (e lst)
      (unless (same-atomic x e)
        (push e res)))
    (nreverse res)))

(defun assoc-atomic (x alist)
  (declare (type t x)
           (list alist)
           (values (or null t)))
  (dolist (e alist nil)
    (when (same-atomic x (car e)) (return e))))

(defun same-atomic (x y)
  (declare (type list x y)
           (values (or null t)))
  (and (consp x) (consp y)
       (term-is-similar? (car x) (car y))
       (term-is-similar? (cdr x) (cdr y)))
  )

(defun elim-supersets (e)
  (declare (type list e)
           (values list))
  (let ((res nil))
    (dolist (x e)
      (unless (dolist (y e nil)
                (when (and (not (eq x y))
                           (substitution-subset y x))
                  (return t)))
        (push x res)))
    res))

(defun make-id-condition-direct (vars subs)
  (declare (type list vars subs)
           (values list))
  (let ((subs2 nil))
    (dolist (sub subs)
      (when sub
        (let ((subcan (substitution-can (substitution-restrict vars sub))))
          (unless (member subcan subs2 :test #'substitution-equal)
            (push subcan subs2)))))
    (if subs2
        (list
         'not
         (rule-make-or-list
          (mapcar #'(lambda (sub)
                      (rule-make-and-list
                       (mapcar #'(lambda (si)
                                   (list 'equal (car si) (cdr si)))
                               sub)))
                  subs2)))
        nil)))

(defun normalize-for-identity-total (tm)
  (declare (type term tm))
  (theory-standard-form (normalize-for-identity tm)))

;;; rules for and or not == =/= identical nonidentical must not have conditions
(defun term-simplify (tm &optional (module *current-module*))
  (declare (type term tm)
           (values (or null term)))
  (if (term-is-variable? tm)
      nil
    (if (term-is-constant? tm)
        nil
      (let ((meth (term-head tm)))
        (dolist (subtm (term-subterms tm))
          (term-simplify subtm module))
        (if (or (eq *BOOL-and* meth)
                (eq *BOOL-or* meth)
                (eq *BOOL-not* meth)
                (eq *BOOL-if* meth))
            (simplify-on-top tm module)
          (if (and (or (eq *BOOL-equal* meth)
                       (eq *BOOL-nonequal* meth)
                       (eq *identical* meth)
                       (eq *nonidentical* meth))
                   (term-is-ground? (term-arg-1 tm))
                   (term-is-ground? (term-arg-2 tm)))
              (if (or (eq *BOOL-equal* meth)
                      (eq *identical* meth))
                  (if (term-is-similar? (term-arg-1 tm) (term-arg-2 tm))
                      (term-replace tm (simple-copy-term *BOOL-true*))
                    nil)
                (if (term-is-similar? (term-arg-1 tm) (term-arg-2 tm))
                    (term-replace tm (simple-copy-term *BOOL-false*))
                  nil))
            nil)))))
  tm)

(defun normalize-for-identity (term)
  (declare (type term term))
  (cond ((or (term-is-variable? term) (term-is-constant? term))
         term)
        (t (let* ((meth (term-head term))
                  (thy (method-theory meth))
                  (id-flag (and (theory-contains-identity thy)
                                (null (cdr (theory-zero thy)))))
                  (id (if id-flag (car (theory-zero thy))))
                  (subs (mapcar #'normalize-for-identity
                                (term-subterms term))))
             (declare (type method meth)
                      (type list thy)
                      (type (or null t) id-flag)
                      (type (or null term) id)
                      (type list subs))
             (if id
                 (if (term-is-similar? (car subs) id)
                     (cadr subs)
                   (if (term-is-similar? (cadr subs) id)
                       (car subs)
                     (make-term-with-sort-check meth subs)))
               (make-term-with-sort-check meth subs))))))
;;; EOF
