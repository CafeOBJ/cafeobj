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
                                 System: CHAOS
                                 Module: deCafe
                                File: view.lisp
==============================================================================|#
#-:chaos-debug
(declaim (optimize (speed 3) (safety 0) #-GCL (debug 0)))
#+:chaos-debug
(declaim (optimize (speed 1) (safety 3) #-GCL (debug 3)))

(declaim (special *modexp-abstract-module*))
(defvar *modexp-abstract-module* nil)

;;; (defvar *on-view-debug* nil)

;;; *******************************
;;; CONSTRUCTING MODMORPH FROM VIEW
;;; *******************************

;;;=============================================================================
;;; VIEWS-TO-MODMORPH : module list-of-args -> ModMorph
;;; using `module' in argument so can get the views used in defintion of module.
;;; list-of-args = ((%!arg arg-name view) ...)
;;;-----------------------------------------------------------------------------

(defun views-to-modmorph (mod args &optional (warn t))
  (let* ((morphs (mapcar #'(lambda (arg)
                             (view->modmorph mod arg))
                         args))
         (m-morph (car morphs)))
    (dolist (m (cdr morphs))
      (setq m-morph (modmorph-merge m-morph m warn)))
    m-morph))

(defun view->modmorph (mod arg)
  (let ((arg-name (%!arg-name arg))) 
    (when (and (consp arg-name)
               (cdr arg-name))
      (setq arg-name
            (cons (car arg-name)
                  ;; also local
                  (eval-modexp (cdr arg-name) t))))
    (let ((ath (find-parameterized-submodule arg-name mod))
          (vw (%!arg-view arg)))
      (when (or (modexp-is-error ath) (null ath))
        (with-output-panic-message ()
          (format t "could not find theory module specified by the argument ~s"
                  (%!arg-name arg))
          (chaos-error 'panic)))
      (convert-view-to-modmorph ath vw))))

;;; CONVERT-VIEW-TO-MODMORPH ath avw
;;; ath -- the actual theory in the parameterized module.
;;; avw -- view.
;;;

(defun convert-view-to-modmorph (ath avw)
  (unless (view-p avw)
    (break "Internal Error : convert-view-to-modmorph: illegal form; incomplete"))
  (unless (eq ath (view-src avw))
    ;; this happens when we give predefined named view as argument.
    ;; reconstruct the real view.
    (setq avw (make-real-view ath avw)))
  ;;
  (let ((modm (acons  ath
                      avw               ; needs to be the view itself
                                        ; to allow proper composition.
                      nil))
        (sortm (view-sort-maps avw))
        (opm (mapcar #'(lambda (x)
                         (if (operator-method-p (car x))
                             ;; no need to convert
                             x
                             (cons (term-head (car x))
                                   `(:replacement ,(term-subterms (car x))
                                     ,(cadr x)))))
                     (view-op-maps avw)))
        (modmorph nil))
    (setq modmorph (create-modmorph `(%map ,ath ,avw) sortm opm modm))
    ;;
    #||
    (when (int-instantiation-p (view-target avw))
      ;; target is another instantiation
      (let ((mappg (views-to-modmorph (int-instantiation-module (view-target avw))
                                      (int-instantiation-args (view-target avw))
                                      nil)))
        (setq modmorph (modmorph-merge modmorph mappg nil))))
    ||#
    modmorph
    ))

;;; MAKE-REAL-VIEW : theory view -> view'
;;; fixes real source theory module in view.
;;; reconstruction
;;;
#||
(defun make-real-view (ath avw)
  (labels ((find-sort-or-error (sort)
             (or (find-sort-in ath (sort-id sort))
               (with-output-chaos-error ('no-such-sort)
                 (format t "constructing view, no such sort ~a in " (sort-id sort))
                 (print-mod-name ath *standard-output* t t)
                 )))
           (find-method-or-error (method)
             (or (find-method-in (method-symbol ath)
                                 (mapcar #'find-sort-or-error (method-arity method))
                                 (find-sort-or-error (method-coarity method)))
                 (with-output-chaos-error ('no-such-sort)
                   (princ "constructing view:")
                   (print-next)
                   (princ "~%no such operator ")
                   (print-chaos-object method)
                   (print-next)
                   (princ "in module ")
                   (print-mod-name ath *standard-output* t t)
                   )))
           )
    (let (sort-mapping
          op-mapping
          new-view)
      (setq sort-mapping
            (mapcar #'(lambda (x)
                        (cons (find-sort-or-error (car x))
                              (cdr x)))
                    (view-sort-maps avw)))
      (setq op-mapping
            (mapcar #'(lambda (x)
                        (cons (term-head (car x))
                              `(:replacement ,(term-subterms (car x)) ,(cdr x))))
                  (mapcar #'(lambda (v)
                              (cons (let ((method (term-head (car v))))
                                      (make-term-check-op
                                       (find-method-or-error method
                                            ath
                                            (method-symbol method)
                                            (mapcar #'(lambda (s)
                                                        (find-sort-in ath
                                                                      (sort-id s)))
                                                    (method-arity method))
                                            (find-sort-in ath
                                                          (sort-id (method-coarity
                                                                    method))))
                                       (term-subterms (car v))))
                                    (cadr v)))
                          (view-op-maps avw))))
      (setq new-view (view-struct* (view-struct-name avw)))
      (setf (view-src new-view) ath)
      (setf (view-target new-view) (view-target avw))
      (setf (view-sort-maps new-view) sort-mapping)
      (setf (view-op-maps new-view) op-mapping)
      (setf (view-decl-form new-view) (view-decl-form avw))
      new-view)))
||#

(defun make-real-view (ath avw)
  (let ((form (view-decl-form avw)))
    (let ((new-view (create-view ath (view-target avw) (%view-map form) nil)))
      (setf (view-name new-view) (view-name avw))
      (setf (view-decl-form new-view) form)
      new-view)))

;;; *****************************************
;;; RESOLVING REFERENCES AND MAPPINGS IN VIEW
;;; *****************************************

;;;=============================================================================
;;; CONSTRUCT VIEW OBJECT
;;;

;;; seems over general in our case. 
;;;
(defun view-map-image-sort (mod x sort-map)
  (let ((val (find-if #'(lambda (v) (sort= x (car v))) sort-map)))
    (if val
        (cdr  val)
        (if (memq x (module-all-sorts mod))
            x
            (let ((val2 (find-sort-in mod (sort-id x))))
              (if val2 val2 x))))))

(defun view-map-image-sorts (mod l sort-map)
  (mapcar #'(lambda (x) (view-map-image-sort mod x sort-map))
          l))

;;;
;;; COMPLETE-VIEW
;;;
(defun complete-view (vw &optional arg-name mod pre-map)
  (let ((view nil)
        (source-module nil))
    ;;
    ;; construct the view object to be used for instantiation process.
    ;;
    (let ((target (if (eq 'none (%view-target vw))
                      (with-output-chaos-error ('modexp-eval)
                        (princ "target module cannot be omitted in view.")
                        )
                      (%view-target vw))))
      ;; evaluate source
      (cond (arg-name                   ;formal argument name --> theory module
             ;; resolve qualification in arg-name
             (when (and (consp arg-name) (cdr arg-name))
               ;; qualified view (arg-name . context)
               (setq arg-name (cons (car arg-name)
                                    ;; also local
                                    (eval-modexp (cdr arg-name) t)))
               (when (modexp-is-error (cdr arg-name))
                 (with-output-chaos-error ('modexp-eval)
                   (format t "error in argument name : no such module ~a." (cdr arg-name))
                   )))
             (setq source-module (find-parameterized-submodule arg-name mod)))
            (t (setq source-module (eval-modexp (%view-module vw) t))))
      (when (modexp-is-error source-module)
        (with-output-chaos-error ('modexp-eval)
          (cond (arg-name
                 (format t "no such parameter ~a" (if (consp arg-name)
                                                      (car arg-name)
                                                      arg-name))
                 (print-next)
                 (princ "in module ")
                 (print-mod-name mod))
                (t (format t "could not evaluate view source module ~a" (%view-module vw))))
          ))
      ;;
      (when (modexp-is-?name? target)
        (setq target (?name-name target)))
      ;; target can be a predefined view name.
      (when (stringp target)
        (setq view (find-view-in-env (normalize-modexp target)))
        (when (and view (view-is-inconsistent view))
          ;; reconstruct from the scratch
          ;; view will be updated by side-effect.
          (eval-modexp (view-decl-form view))
          ;; set dependency relation
          (add-depend-relation mod :view view)))
      ;;
      (if view
          view
          ;; we construct a brand new view object.
          (progn
            (setq view (create-view source-module
                                    target
                                    (%view-map vw)
                                    pre-map))
            (mark-view-as-consistent view)
            (setf (view-decl-form view) vw)
            view)))))

;;;
;;; CREATE-VIEW
;;;
(defun principal-sort (module)
  (or (module-principal-sort module)
      (let ((sorts (module-all-sorts module)))
        (if (null (cdr sorts))
            (car sorts)
            (if (not (module-is-hard-wired module))
                (progn
                  (setq sorts
                        (remove-if #'(lambda (x) (module-is-hard-wired (sort-module x)))
                                   sorts))
                  (if (null (cdr sorts))
                      (car sorts)
                      nil))
                nil)))))

#||
(defun create-view (th mod rename-map)
  (let ((vw-map (if (%is-rmap rename-map)
                    (%rmap-map rename-map)
                    rename-map)))
    ;;
    ;; eval source & target module
    ;;
    (let ((src-mod (eval-modexp th t))   ; should already evaluated but..
          (dst-mod (eval-modexp mod t))) ; really evaluate the target.
      (when (or (modexp-is-error src-mod) (modexp-is-error dst-mod))
        ;; error, ivalid args as modules
        (with-output-chaos-error ('modexp-eval)
          (princ "Cannot evaluate module in view: ")
          (when (modexp-is-error src-mod)
            (princ "view source = ")
            (print-modexp th))
          (when (modexp-is-error dst-mod)
            (when (modexp-is-error src-mod)
              (princ ", and "))
            (princ "view target = ")
            (print-modexp mod))
          ))
      ;;
      ;; compute mappings.
      ;;
      (let ((sort-maps (cadr (assq '%ren-sort vw-map)))
            (op-maps   (cadr (assq '%ren-op vw-map)))
            (hsort-maps (cadr (assq '%ren-hsort vw-map)))
            (bop-maps (cadr (assq '%ren-bop vw-map)))
            (vars (cadr (assq '%vars vw-map)))
            (pr (principal-sort src-mod))
                                        ; NOW we support. May/'97
            )
        ;;
        ;; ** compute sort mappings ---------------------------------
        ;;
        (let ((sort-mapping (compute-sort-mappings src-mod
                                                   dst-mod
                                                   sort-maps
                                                   hsort-maps)))
          ;; make sort mappings with completing sort maps not explicitly
          ;; specified.
          (dolist (s (module-all-sorts src-mod))
            (unless (*find-sort-in-map sort-mapping s)
              ;; map is not specified.
              (let ((val (find-sort-in dst-mod (sort-id s) t)))
                (when (eq s pr)         ; is this the principal sort?
                  (let ((pval (principal-sort dst-mod)))
                    (when pval
                      (setq val pval))))
                ;; find compatible same name sort ---
                ;; should check types,i.e., visible & hidden.
                (if val
                    (unless (sort= s val)
                      (push (cons s val) sort-mapping))
                    (with-output-chaos-warning ()
                      (princ "view incomplete for sort ")
                      (print-chaos-object s)
                      (print-next)
                      (princ "view from ")
                      (print-chaos-object src-mod)
                      (princ " to ")
                      (print-chaos-object dst-mod)
                      (print-next)
                      (princ "!! MAY BE HARMFUL !!")
                      ;; (chaos-error 'modexp-eval)
                      )
                    )
                )))
          ;;
          ;; ** compute operator mapping ------------------------------------
          ;;
          (let* ((src-vars
                  (mapcan #'(lambda (x)
                              (let ((sort (find-sort-in src-mod
                                                        (cadr x))))
                                (unless sort
                                  (with-output-chaos-error ('modexp-eval)
                                    (format t "sort ~a not found in view variable"
                                            (cadr x))
                                    ))
                                (mapcar #'(lambda (y)
                                            (make-variable-term sort
                                                                (if (stringp y)
                                                                    (intern y)
                                                                    y)))
                                        (car x))))
                          vars))
                 (dst-vars
                  (mapcar #'(lambda (x)
                              (let ((val (cdr (assq (variable-sort x)
                                                    sort-mapping))))
                                (if val
                                    (make-variable-term val (variable-name x))
                                    x)))
                          src-vars))
                 ;;
                 (op-mapping (compute-op-mappings src-mod
                                                  dst-mod
                                                  sort-mapping
                                                  op-maps
                                                  bop-maps
                                                  src-vars
                                                  dst-vars
                                                  )))
            ;; now op-mapping is in form of ( op-map ... ),
            ;; where op-map is
            ;;       (source-pattern target-pattern)
            ;; this will be converted to operator map of modmorhp:
            ;;       (method :replacement List[psuedo-var] target-pattern)
            ;;    >> *NOTE* we do not use ':simple-map for view.
            ;; we are now about to complete method mapping.
            ;;    >> *NOTE* handle constants last.
            ;; make method map with the same name iff not mapped already.
            ;;
            (dolist (oinfo (module-all-operators src-mod))
              (dolist (method (opinfo-methods oinfo))
                (block next-method
                  (let ((target-method nil))
                    (when (and
                           (or (method-is-user-defined-error-method method)
                               (not (method-is-error-method method)))
                           (let ((xmod (method-module method)))
                             (not
                              (memq xmod *kernel-hard-wired-builtin-modules*))
                             ))
                      (unless (*find-method-in-map op-mapping method)
                        ;;
                        ;; not in the map
                        ;;
                        (when *on-view-debug*
                          (format t "~%[create-view] :")
                          (format t "~&-find non-specified method ")
                          (print-method method)
                          (format t "~&-try finding in module ")
                          (print-mod-name dst-mod))
                        ;; find in destination module with
                        ;; name, arity and coarity mapped by sort-map.
                        (unless (sort= (method-coarity method) *sort-id-sort*)
                          (setq target-method
                                (find-method-in dst-mod
                                                (method-symbol method)
                                                (view-map-image-sorts
                                                 dst-mod
                                                 (method-arity method)
                                                 sort-mapping)
                                                (view-map-image-sort
                                                 dst-mod
                                                 (method-coarity method)
                                                 sort-mapping)))
                          (unless target-method
                            ;; failed to find.
                            ;; we continue, but may cause big problem later
                            ;; so gives a warning.
                            (with-output-chaos-warning ()
                              (princ "view incomplete for operator ")
                              (print-method method)
                              (princ " of ")
                              (print-mod-name src-mod)
                              (print-next)
                              (princ "view to ")
                              (print-mod-name dst-mod)
                              (print-next)
                              (princ "!! MAY CAUSE PANIC LATER !!"))
                            (return-from next-method nil)
                            )

                          ;;
                          ;; found the target-method in dst-mod,
                          ;; i.e., with the same name & has proper rank.
                          ;;
                          (unless (eq method target-method)
                            ;; construct map iff they are different object.
                            (let ((vars (make-psuedo-vars-from-sorts
                                         (method-arity method))))
                              (when *on-view-debug*
                                (format t "~%-*creating new op-mapping ")
                                (format t "~& from ")
                                (print-method method)
                                (format t "~& to ")
                                (print-method target-method))
                              (push (list (make-term-check-op method vars src-mod)
                                          (make-term-check-op target-method
                                                              vars
                                                              dst-mod))
                                    op-mapping)
                              )
                            ;;
                            (let ((thy1 (method-theory method
                                                       (module-opinfo-table src-mod)))
                                  (thy2 (method-theory target-method
                                                       (module-opinfo-table dst-mod))))
                              (let ((z1 (car (theory-zero thy1)))
                                    (z2 (car (theory-zero thy2))))
                                (when (and z1
                                           (not (*find-method-in-map op-mapping
                                                                     (term-head z1)))
                                           z2
                                           (term-is-constant? z1)
                                           (term-is-constant? z2))
                                  (push (list z1 z2)
                                        op-mapping))))))))))))
            ;;
            ;; make SortId op mappings
            ;;
            (let ((s-op nil)
                  (t-op nil)
                  (ignore-these (list *cosmos* *universal-sort*
                                      *huniversal-sort* *bottom-sort*)))
              (dolist (s-map sort-mapping)
                (let ((source (car s-map))
                      (target (cdr s-map)))
                  (break)
                  (unless (or (err-sort-p source)
                              (memq source ignore-these)
                              (memq target ignore-these))
                    (setq s-op (find-method-in src-mod
                                               (string (sort-id source))
                                               nil
                                               *sort-id-sort*))
                    (unless (*find-method-in-map op-mapping s-op)
                      (setq t-op (find-method-in dst-mod
                                                 (string (sort-id target))
                                                 nil
                                                 *sort-id-sort*))
                      (push (list (make-term-check-op s-op nil src-mod)
                                  (make-term-check-op t-op nil dst-mod))
                            op-mapping))))))
            
            ;;
            ;; final result
            ;;
            (let ((view (view-struct* :anon-view)))
              (initialize-view view)
              (setf (view-src view) src-mod
                    (view-target view) dst-mod
                    (view-sort-maps view) sort-mapping
                    (view-op-maps view) op-mapping)
              ;;
              (when *on-view-debug*
                (format t "~%[generated view]:")
                (format t "~& source = ") (print-chaos-object src-mod)
                (format t "~& target = ") (print-chaos-object dst-mod)
                (format t "~& sort-map = ")
                (dolist (smap sort-mapping)
                  (terpri)
                  (print-chaos-object smap))
                (format t "~& op-map =")
                (dolist (opmap op-mapping)
                  (terpri)
                  (print-term-method (car opmap))
                  (princ " --> ")
                  (princ (cdr opmap))
                  ;; (print-chaos-object opmap)
                  ))
              ;;
              view)
            ))))))

||#

(defun create-view (th mod rename-map pre-map)
  (let ((vw-map (if (%is-rmap rename-map)
                    (%rmap-map rename-map)
                    rename-map)))
    ;;
    ;; eval source & target module
    ;;
    (let ((src-mod (eval-modexp th t))   ; should already evaluated but..
          (dst-mod (eval-modexp mod t))) ; really evaluate the target.
      (when (or (modexp-is-error src-mod) (modexp-is-error dst-mod))
        ;; error, ivalid args as modules
        (with-output-chaos-error ('modexp-eval)
          (princ "Cannot evaluate module in view: ")
          (when (modexp-is-error src-mod)
            (princ "view source = ")
            (print-modexp th))
          (when (modexp-is-error dst-mod)
            (when (modexp-is-error src-mod)
              (princ ", and "))
            (princ "view target = ")
            (print-modexp mod))
          ))
      ;;
      ;; compute mappings.
      ;;
      (let ((pre-sort-mapping nil)
            (pre-op-mapping nil)
            )
        ;;
        (when pre-map
          (setq pre-sort-mapping (modmorph-sort pre-map))
          (setq pre-op-mapping (modmorph-op pre-map)))
        #||
        (when (int-instantiation-p dst-mod)
          (let ((mappg (views-to-modmorph (int-instantiation-module dst-mod)
                                          (int-instantiation-args dst-mod))))
            (setq pre-sort-mapping (modmorph-sort mappg))
            (setq pre-op-mapping (modmorph-op mappg))))
        ||#
        ;;

        (let ((sort-maps (cadr (assq '%ren-sort vw-map)))
              (op-maps   (cadr (assq '%ren-op vw-map)))
              (hsort-maps (cadr (assq '%ren-hsort vw-map)))
              (bop-maps (cadr (assq '%ren-bop vw-map)))
              (vars (cadr (assq '%vars vw-map)))
              (pr (principal-sort src-mod))
                                        ; NOW we support. May/'97
              )
          ;;
          ;; ** compute sort mappings ---------------------------------
          ;;
          (let ((sort-mapping (compute-sort-mappings src-mod
                                                     dst-mod
                                                     sort-maps
                                                     hsort-maps)))
            #||
            (when pre-sort-mapping
              (setq sort-mapping
                    (modmorph-merge-assoc sort-mapping pre-sort-mapping nil)))
            ||#
            ;; make sort mappings with completing sort maps not explicitly
            ;; specified.
            (dolist (s (module-all-sorts src-mod))
              (unless (*find-sort-in-map sort-mapping s)
                ;; map is not specified.
                ;; we prefer map in pre-sort-mapping iff given.
                (let ((pre (assq s pre-sort-mapping)))
                  (if pre
                      (push pre sort-mapping)
                      ;; else find by `the same name principle.'
                      (let ((val (find-sort-in dst-mod (sort-id s) t)))
                        (when (eq s pr) ; is this the principal sort?
                          (let ((pval (principal-sort dst-mod)))
                            (when pval
                              (setq val pval))))
                        ;; find compatible same name sort ---
                        ;; should check types,i.e., visible & hidden.
                        (if val
                            (unless (sort= s val)
                              (push (cons s val) sort-mapping))
                            (with-output-chaos-warning ()
                              (princ "view incomplete for sort ")
                              (print-chaos-object s)
                              (print-next)
                              (princ "view from ")
                              (print-chaos-object src-mod)
                              (princ " to ")
                              (print-chaos-object dst-mod)
                              (print-next)
                              (princ "!! this can cause panic.")
                              ;; (chaos-error 'modexp-eval)
                              )))
                      ))))
            ;;
            ;; ** compute operator mapping ------------------------------------
            ;;
            (let* ((src-vars
                    (mapcan #'(lambda (x)
                                (let ((sort (find-sort-in src-mod
                                                          (cadr x))))
                                  (unless sort
                                    (with-output-chaos-error ('modexp-eval)
                                      (format t "sort ~a not found in view variable"
                                              (cadr x))
                                      ))
                                  (mapcar #'(lambda (y)
                                              (make-variable-term sort
                                                                  (if (stringp y)
                                                                      (intern y)
                                                                      y)))
                                          (car x))))
                            vars))
                   (dst-vars
                    (mapcar #'(lambda (x)
                                (let ((val (cdr (assq (variable-sort x)
                                                      sort-mapping))))
                                  (if val
                                      (make-variable-term val (variable-name x))
                                      x)))
                            src-vars))
                   ;;
                   (op-mapping (compute-op-mappings src-mod
                                                    dst-mod
                                                    sort-mapping
                                                    op-maps
                                                    bop-maps
                                                    src-vars
                                                    dst-vars
                                                    )))
              #||
              (when pre-op-mapping
                (setq op-mapping
                      (modmorph-merge-op-assoc op-mapping
                                               pre-op-mapping)))
              ||#
              ;; now op-mapping is in form of ( op-map ... ),
              ;; where op-map is
              ;;       (source-pattern target-pattern)
              ;; this will be converted to operator map of modmorhp:
              ;;       (method :replacement List[psuedo-var] target-pattern)
              ;;    >> *NOTE* we do not use ':simple-map for view.
              ;; we are now about to complete method mapping.
              ;;    >> *NOTE* handle constants last.
              ;; make method map with the same name iff not mapped already.
              ;;
              (dolist (oinfo (module-all-operators src-mod))
                (dolist (method (opinfo-methods oinfo))
                  (block next-method
                    (let ((target-method nil))
                      (when (and
                             (or (method-is-user-defined-error-method method)
                                 ;; t
                                 (not (method-is-error-method method)))
                             (let ((xmod (method-module method)))
                               (not
                                (memq xmod *kernel-hard-wired-builtin-modules*))
                               ))
                        (unless (*find-method-in-map op-mapping method)
                          ;;
                          ;; not in the map
                          ;;
                          (when *on-view-debug*
                            (format t "~%[create-view] :")
                            (format t "~&-find non-specified method ")
                            (print-method method)
                            (format t "~&-try finding in module ")
                            (print-mod-name dst-mod))
                          ;; check in pre-op-mapping,
                          ;; if found use this map.
                          (let ((pre (*find-method-in-map pre-op-mapping method)))
                            (if pre
                                (push pre op-mapping)
                                ;; find in destination module with
                                ;; name, arity and coarity mapped by sort-map.
                                (unless (sort= (method-coarity method)
                                               *sort-id-sort*)
                                  (setq target-method
                                        (find-method-in dst-mod
                                                        (method-symbol method)
                                                        (view-map-image-sorts
                                                         dst-mod
                                                         (method-arity method)
                                                         sort-mapping)
                                                        (view-map-image-sort
                                                         dst-mod
                                                         (method-coarity method)
                                                         sort-mapping)))
                                  (unless target-method
                                    ;; failed to find.
                                    ;; we continue, but may cause big problem later
                                    ;; so gives a warning.
                                    (with-output-chaos-warning ()
                                      (princ "view incomplete for operator ")
                                      (print-method method)
                                      (princ " of ")
                                      (print-mod-name src-mod)
                                      (print-next)
                                      (princ "view to ")
                                      (print-mod-name dst-mod)
                                      (print-next)
                                      (princ "can cause panic later !!"))
                                    (return-from next-method nil)
                                    )
                                  ;;
                                  ;; found the target-method in dst-mod,
                                  ;; i.e., with the same name & has proper rank.
                                  ;;
                                  (unless (eq method target-method)
                                    ;; construct map iff they are different object.
                                    (let ((vars (make-psuedo-vars-from-sorts
                                                 (method-arity method))))
                                      (when *on-view-debug*
                                        (format t "~%-*creating new op-mapping ")
                                        (format t "~& from ")
                                        (print-method method)
                                        (format t "~& to ")
                                        (print-method target-method))
                                      (push (list (make-term-check-op
                                                   method
                                                   vars
                                                   src-mod)
                                                  (make-term-check-op
                                                   target-method
                                                   vars
                                                   dst-mod))
                                            op-mapping)
                                      )
                                    ;;
                                    (let ((thy1 (method-theory
                                                 method
                                                 (module-opinfo-table src-mod)))
                                    (thy2 (method-theory
                                           target-method
                                           (module-opinfo-table dst-mod))))
                                (let ((z1 (car (theory-zero thy1)))
                                      (z2 (car (theory-zero thy2))))
                                  (when (and z1
                                             (not (*find-method-in-map
                                                   op-mapping
                                                   (term-head z1)))
                                             z2
                                             (term-is-constant? z1)
                                             (term-is-constant? z2))
                                    (push (list z1 z2)
                                          op-mapping))))))))))))))
              ;;
              ;; make SortId op mappings
              ;;
              (let ((s-op nil)
                    (t-op nil))
                (dolist (s-map sort-mapping)
                  (let ((source (car s-map))
                        (target (cdr s-map))
                        (ignore-these (list *cosmos* *universal-sort*
                                            *huniversal-sort* 
                                            *bottom-sort*)))
                    (unless (or (err-sort-p source)
                                (memq source ignore-these)
                                (memq target ignore-these))
                      (setq s-op (find-method-in src-mod
                                                 (string (sort-id source))
                                                 nil
                                                 *sort-id-sort*))
                      (unless (*find-method-in-map op-mapping s-op)
                        (setq t-op (find-method-in dst-mod
                                                   (string (sort-id target))
                                                   nil
                                                   *sort-id-sort*))
                        (push (list (make-term-check-op s-op nil src-mod)
                                    (make-term-check-op t-op nil dst-mod))
                              op-mapping))))))
              ;;
              ;; final result
              ;;
              (let ((view (view-struct* :anon-view)))
                (initialize-view view)
                (setf (view-src view) src-mod
                      (view-target view) dst-mod
                      (view-sort-maps view) sort-mapping
                      (view-op-maps view) op-mapping)
                ;;
                (when *on-view-debug*
                  (format t "~%[generated view]:")
                  (format t "~& source = ") (print-chaos-object src-mod)
                  (format t "~& target = ") (print-chaos-object dst-mod)
                  (format t "~& sort-map = ")
                  (dolist (smap sort-mapping)
                    (terpri)
                    (print-chaos-object smap))
                  (format t "~& op-map =")
                  (dolist (opmap op-mapping)
                    (terpri)
                    (print-term-method (car opmap))
                    (princ " --> ")
                    (princ (cdr opmap))
                    ;; (print-chaos-object opmap)
                    ))
                ;;
                view)
              )))))))

(defun *find-sort-in-map (map x)
  (let ((imap (find-if #'(lambda (y)
                           (sort= x (car y)))
                       map)))
    (if imap
        (cdr imap)
        nil)))

(defun *find-method-in-map (op-mapping method)
  ;;
  (find-if #'(lambda (x) (if (operator-method-p (car x))
                             (eq method (car x))
                             (eq method (term-head (car x)))))
           op-mapping))

;;; ***********************
;;; COMPUTING REAL MAPPINGS
;;; ***********************

;;; COMPUTE-SORT-MAPPINGS : src-mod dst-mod sort-maps -> sort-mapping
;;;  resolve sort mapping specified by sort-maps
;;; src-mod : source module
;;; dst-mod : target module
;;; sort-maps : list of (from to).
;;;
;;; returns the list of (from . to).
;;; there are no errors.
;;;
(defun compute-sort-mappings (src-mod dst-mod sort-maps hsort-maps)
  (let ((res (nconc (mapcan
                     #'(lambda (x)
                         (compute-sort-mapping src-mod dst-mod x :visible))
                     sort-maps)
                    (mapcan
                     #'(lambda (x)
                         (compute-sort-mapping src-mod dst-mod x :hidden))
                     hsort-maps)))
        (f-so (module-sort-order src-mod))
        (t-so (module-sort-order dst-mod))
        (err-map nil))
    ;; make implicit mapping for error sorts, if not specified.
    (dolist (map res)
      (let ((s-err (the-err-sort (car map) f-so))
            (t-err (the-err-sort (cdr map) t-so)))
        (unless (assq s-err res)
          (push (cons s-err t-err) err-map))))
    (when err-map
      (setq res (nconc res err-map)))
    ;;
    res))

(defun compute-sort-mapping (src-mod dst-mod sort-map &optional (type :visible))
  (let ((srcs (find-sort-in src-mod (car sort-map)))
        (tgts (find-sort-in dst-mod (cadr sort-map))))
    (unless srcs
      (with-output-chaos-error ('modexp-eval)
        (princ "in view from ")
        (print-mod-name src-mod)
        (princ " to ")
        (print-mod-name dst-mod)
        (print-next)
        (princ "source sort not recognized : ")
        (print-sort-ref (car sort-map))
        ))
    (unless tgts
      (with-output-chaos-error ('modexp-eval)
        (princ "in view from ")
        (print-mod-name src-mod)
        (princ " to ")
        (print-mod-name dst-mod)
        (print-next)
        (princ "target sort not recognized: ")
        (print-sort-ref (cadr sort-map))
        ))
    (case type
      (:visible (unless (and (sort-is-visible srcs)
                             (sort-is-visible tgts))
                  (with-output-chaos-error ('invalid-map)
                    (format t "both source(~A) and target(~A) sorts must be visible for `sort' map"
                            (sort-id srcs)
                            (sort-id tgts))
                    )))
      (otherwise (unless (and (sort-is-hidden srcs)
                              (sort-is-hidden tgts))
                   (with-output-chaos-error ('invalid-map)
                     (format t "both source(~A) and target(~A) sort must be hidden for `hsort' map."
                             (sort-id srcs)
                             (sort-id tgts))
                     ))))
    ;;
    (list (cons srcs tgts))))

;;; COMPUTE-OP-MAPPINGS : src-mod dst-mod op-maps bop-maps src-vars dst-vars
;;;                       -> method-mapping
;;; resolve operator mapping specified by view.
;;;
;;; src-mod   : source module object.
;;; dst-mod   : target module object.
;;; sort-maps : list of sort rename map in solved form, ((from . to) ...)
;;; op-maps   : list of operator rename map to be solved
;;;             ((from to) ....)
;;;             i.e., still in non resolved form (:opref).
;;; bop-maps  : similar to op-maps, but maps between behavioural operators.
;;;
;;; result method mapping will be in the form of
;;;  ((from to) .....)
;;; where from is operator-method
;;;       to is one of the followings:
;;;       a) :simple-map 

(defun compute-op-mappings (src-mod dst-mod sort-maps op-maps bop-maps src-vars dst-vars)
  (nconc (mapcan #'(lambda (opmap)
                     (compute-op-mapping src-mod
                                         dst-mod
                                         sort-maps
                                         opmap
                                         src-vars
                                         dst-vars
                                         :functional
                                         ))
                 op-maps)
         (mapcan #'(lambda (opmap)
                     (compute-op-mapping src-mod
                                         dst-mod
                                         sort-maps
                                         opmap
                                         src-vars
                                         dst-vars
                                         :behavioural
                                         ))
                 bop-maps)))

(defun resolve-op-pattern-as-term (mod pat vars)
  (let ((pparsed (let ((*parse-variables* (mapcar #'(lambda (x)
                                                      (cons (variable-name x) x))
                                                  vars)))
                   (if (and (term? pat)
                            (term-is-application-form? pat))
                       pat
                     (parse-quiet-parse mod pat))
                   )
          ))
    (if (term-is-an-error pparsed)
        (when *on-view-debug*
          (with-in-module (mod)
            (print-term-tree pparsed)
          nil))
        (if (term-is-builtin-constant? pparsed)
            (values pparsed
                    (term-builtin-value pparsed)
                    nil
                    nil)
            (values pparsed
                    (term-head pparsed)
                    (term-variables pparsed)
                    (make-psuedo-vars (term-subterms pparsed)))
            ))))

(defun split-str (str)
  (let ((len (length str))
        (index 0)
        (r nil))
    (dotimes (i len (progn (unless (= index len)
                             (push (subseq str index) r))
                           (reverse r)))
      (when (char= (char str i) #\_)
        (unless (= index i)
          (push (subseq str index i) r))
        (push "_" r)
        (setf index (1+ i)))
      )))
             
(defun delimit-op-pat (pat)
  (let ((res nil))
    (dolist (p pat)
      (setf res (nconc res (split-str p))))
    res))

(defun resolve-op-pattern-as-reference (mod pat)
  (setq pat (delimit-op-pat pat))
  (let ((*modexp-parse-input* (append pat '(".")))
        (new-pat nil)
        (info nil)
        (res nil))
    (setq new-pat (parse-operator-reference '(".")))
    (setq info (find-qual-operators new-pat mod))
    #||
    (when (cdr info)
      (with-output-chaos-warning ()
        (format t "operator reference ~A is ambiguous" pat)
        ;;(print-ast new-pat)
        (print-next)
        (princ "in the context: ")
        (print-mod-name mod *standard-output* t)
        ))
    ||#
    ;; we only need methods
    (dolist (i info)
      (dolist (m (opinfo-methods i))
        (push m res)))
    (if res
        (list 'dummy-op (nreverse res))
        nil)))
        
(defun compute-op-mapping (src-mod dst-mod sort-maps op-map src-vars dst-vars
                                   &optional (type :functional))
  (let ((src-opex (car op-map))
        (dst-opex (cadr op-map))
        (src-opinfo nil)
        (dst-opinfo nil)
        (mappings nil)
        (source-map-type :term)
        (target-map-type :term)
        )
    (multiple-value-bind (src-pat src-method src-varbs src-p-vars)
        ;;
        ;; source op pattern
        ;;
        ;; first we assume pattern is given as term.
        (resolve-op-pattern-as-term src-mod src-opex src-vars)
      ;;
      (when src-pat
        (unless (every #'(lambda (x) (term-is-variable? x))
                       (term-subterms src-pat))
          (with-output-chaos-error ('invalid-op-map)
            (princ "mapping operator: ")
            (print-method (term-head src-pat))
            (print-next)
            (princ "source pattern must not have non-variable subterms:")
            ))
        ;; construct a generic pattern with psuedo variables:
        (unless (term-is-builtin-constant? src-pat)
          (setq src-pat
                (make-term-check-op src-method src-p-vars src-mod)))
        (setq source-map-type :term))
      ;;
      ;; also try,
      ;; given source op pattern may be a operator reference.
      ;;
      (unless src-pat
        (setq src-opinfo (resolve-op-pattern-as-reference src-mod src-opex)))
      (if src-opinfo
          (setq source-map-type :op-ref)
          (unless src-pat
            (with-output-chaos-error ('invalid-map)
              (format t "could not resolve source operator pattern : ~a"
                      src-opex)
              )))
      ;;
      ;; target pattern
      ;;
      (multiple-value-bind (dst-pat dst-method dst-varbs dst-p-vars)
          (if src-pat
              (resolve-op-pattern-as-term dst-mod dst-opex dst-vars)
              nil)
        (declare (ignore dst-method dst-p-vars))
        (when dst-pat
          ;; construct generic target pattern:
          ;; replaces 
          (let ((subst nil)
                (src-vn (mapcar #'(lambda (x) (variable-name x))
                                src-varbs)))
            (dolist (dv dst-varbs)
              (let* ((vm (variable-name dv))
                     (vpos (position-if #'(lambda (x) (equal vm x)) src-vn)))
                (if vpos (push (cons dv (nth vpos src-p-vars)) subst))))
            (setq dst-pat
                  (substitution-simple-image subst dst-pat))
            (setq target-map-type :term)))
        ;;
        (when src-opinfo
          (setq dst-opinfo (resolve-op-pattern-as-reference dst-mod dst-opex))
          (if dst-opinfo
              (setq target-map-type :op-ref)
              (unless dst-pat
                (with-output-chaos-error ('invalid-map)
                  (format t "could not resolve operator target pattern : ~a"
                          dst-opex)
                  ))))
        ;;
        ;; make mapping
        ;;
        (cond ((and src-opinfo dst-opinfo)
               ;; construct mappings, target must be always a term.
               (let ((tm-list (opinfo-methods dst-opinfo)))
                 (dolist (sm (opinfo-methods src-opinfo))
                   (when (or (method-is-user-defined-error-method sm)
                             (not (method-is-error-method sm)))
                     (let ((tm (find-method-mapped sm
                                                   sort-maps
                                                   tm-list
                                                   src-mod
                                                   dst-mod)))
                       (if tm
                           (let ((vars (make-psuedo-vars-from-sorts
                                        (method-arity sm))))
                             (push (list (make-term-check-op sm vars src-mod)
                                         (make-term-check-op tm vars dst-mod))
                                   mappings))
                           ;; 
                           (with-output-chaos-error ('modexp-eval)
                             (format t "Operator mapping is not injective, the declaration")
                             (print-next)
                             (print-method sm src-mod)
                             (print-next)
                             (princ "has no proper image in the target,")
                             (print-next)
                             (princ "wrt the sort mappings:")
                             (let ((*print-indent* (+ 2 *print-indent*)))
                               (dolist (smap sort-maps)
                                 (print-next)
                                 (print-sort-name (car smap) src-mod)
                                 (princ " --> ")
                                 (print-sort-name (cdr smap) dst-mod)))
                             )))))))
              ((and src-pat dst-pat)
               ;; must check rank is properly mapped.
               (let ((src-method (if (term-is-applform? src-pat)
                                     (term-head src-pat)
                                     nil))
                     (dst-method (if (term-is-applform? dst-pat)
                                     (term-head dst-pat)
                                     nil)))
                 (declare (ignore dst-method))
                 (let ((coarity-mapped (*image-rename-sort sort-maps
                                                           (term-sort src-pat)))
                       (arity-mapped (if src-method
                                         (*image-rename-sorts sort-maps
                                                              (method-arity
                                                               src-method))
                                         nil)))
                   (declare (ignore arity-mapped))
                   (unless (sort= coarity-mapped (term-sort dst-pat))
                     (with-output-chaos-warning ()
                     (princ "operator mapping is not strict wrt sort map:")
                     (print-next)
                     (princ "* sort map")
                     (print-next)
                     (princ "- ")
                     (print-sort-name (term-sort src-pat) src-mod)
                     (princ " --> ")
                     (print-sort-name coarity-mapped dst-mod)
                     (print-next)
                     (princ "* operator map")
                     (print-next)
                     (princ "- source: ")
                     (with-in-module (src-mod)
                       (cond ((term-is-applform? src-pat)
                              (print-chaos-object (term-head src-pat)))
                             ((term-is-builtin-constant? src-pat)
                              (print-chaos-object src-pat)
                              (princ " : ")
                              (print-sort-name (term-sort src-pat)))
                             (t (print-chaos-object src-pat))))
                     (print-next)
                     (princ "- target: ")
                     (with-in-module (dst-mod)
                       (cond ((term-is-applform? dst-pat)
                              (print-chaos-object (term-head dst-pat)))
                             ((term-is-builtin-constant? dst-pat)
                              (print-chaos-object dst-pat)
                              (princ " : ")
                              (print-sort-name (term-sort dst-pat)))
                             (t (print-chaos-object dst-pat)))))))
                 )
               ;; construct complex pattern mapping
               (push (list src-pat dst-pat) mappings))
              ;;; *************
              (t (with-output-chaos-error ('modexp-eval)
                   ;; some useful message will going here....
                   (princ "source and target of operator mapping must be the same type:")
                   (print-next)
                   (format t "- source type: ~a, target type: ~a"
                           (if (eq source-map-type :term)
                               'term
                               "operator name")
                           (if (eq target-map-type :term)
                               'term
                               "operator name"))
                   )
                 ))))
    (when *on-view-debug*
      (format t "~%[compute op mapping]:")
      (let* ((*print-indent* (+ *print-indent* 2))
             (map (car mappings))
             (src (first map))
             (pvars (term-subterms src))
             (dst (second map)))
        (with-in-module (src-mod)
          (print-next)
          (princ "src-pattern : ")
          (if (term-is-builtin-constant? src)
              (progn (term-print src)
                     (format t " of built-in sort ")
                     (print-sort-name (term-sort src)))
              (print-method (term-head src)))
          (print-next)
          (princ "p-vars : ")
          (print-chaos-object pvars))
        (with-in-module (dst-mod)
          (print-next)
          (princ "tgt-pattern : ")
          (if (term-is-builtin-constant? dst)
              (progn (term-print dst)
                     (format t " of built-in sort ")
                     (print-sort-name (term-sort dst)))
              (print-method (term-head dst)))
          (princ "(") (princ dst) (princ ")"))
        ))
    ;; check all at once
    (let ((error nil))
      (dolist (map mappings)
        (let ((src (first map))
              (dst (second map)))
          (case type
            (:functional                ; both should be functional operators
             (unless (and (term-is-of-functional? src)
                          (term-is-of-functional? dst))
               (with-output-simple-msg ()
                 (format t "[Error] source and target must be non-behavioural for `op' map:")
                 (format t "~&- source ") (print-term-method src src-mod)
                 (format t "~&- target ") (print-term-method dst dst-mod)
                 (setq error t))))
            (otherwise
             (unless (and (term-is-of-behavioural*?  src (module-opinfo-table
                                                          src-mod))
                          (term-is-of-behavioural*? dst (module-opinfo-table
                                                         dst-mod)))
               (with-output-simple-msg ()
                 (format t "[Error] source and target must be behavioural for `bop' map:")
                 (format t "~&- source ") (print-term-method src src-mod)
                 (format t "~&- target ") (print-term-method dst dst-mod)
                 (setq error t)))))))
      (when error (chaos-to-top)))
    ;; 
    mappings))

(defvar *view-map-operator-strictly* nil)

(defun find-method-mapped (src-method sort-maps method-list src-mod dst-mod)
  (macrolet ((is-similar-theory? (th1_? th2_?)
               (once-only (th1_? th2_?)
                 ` (and (if (theory-contains-associativity ,th1_?)
                            (theory-contains-associativity ,th2_?)
                            t)
                        (if (theory-contains-commutativity ,th1_?)
                            (theory-contains-commutativity ,th2_?)
                            t)
                        (if (theory-contains-identity ,th1_?)
                            (theory-contains-identity ,th2_?)
                            t)))))
    (flet ((filter-method (arity coarity theory so)
             (declare (ignore theory))
             (remove-if-not
                  #'(lambda (method)
                      (and (if *view-map-operator-strictly*
                               (sort= (method-coarity method) coarity)
                               (sort<= (method-coarity method) coarity so))
                           (if *view-map-operator-strictly*
                               (sort-list= (method-arity method) arity)
                               (sort-list<= (method-arity method) arity so))
                           #|| ignore operator theory now. 
                           (is-similar-theory? theory
                                               (method-theory method
                                                              (module-opinfo-table
                                                               dst-mod)))
                           ||#
                           ))
                  method-list))
           (most-general-method (methods sort-order)
             (when *on-view-debug*
               (format t "~&[most-general-method]")
               (dolist (x methods)
                 (print-next)
                 (princ "- ")
                 (print-chaos-object x)))
             (let ((res (car methods)))
               (dolist (x (cdr methods))
                 (when (method< x res sort-order)
                   (setq res x)))
               (when *on-view-debug*
                 (format t "~%* result = ")
                 (print-chaos-object res))
               res)))
      ;;
      (let ((coarity (*image-rename-sort sort-maps (method-coarity src-method)))
            (arity (*image-rename-sorts sort-maps (method-arity src-method)))
            (theory (method-theory src-method (module-opinfo-table src-mod)))
            (sort-order (module-sort-order dst-mod)))
        (let ((val (filter-method arity coarity theory sort-order))
              (result nil))
          (if (and val (null (cdr val)))
              (setq result (car val))
              (if val
                  (setq result (most-general-method val sort-order))
                  (progn
                    (setq arity (find-sorts-image* (method-arity src-method)
                                                   sort-maps
                                                   dst-mod))
                    (setq coarity (find-sort-image*
                                   (method-coarity src-method)
                                   sort-maps
                                   dst-mod))
                    (setq val (filter-method arity coarity theory sort-order))
                    (if (and val (null (cdr val)))
                        (setq result (car val))
                        (if (cdr val)
                            (setq result (most-general-method val sort-order))
                            (setq result nil))))))
          ;;
          (when result
            (unless (and (sort= (method-coarity result) coarity)
                         (sort-list= (method-arity result) arity))
              (with-output-chaos-warning ()
                (princ "operator mapping is not strict wrt sort map:")
                (print-next)
                (princ "* sort map")
                (dotimes (x (length arity))
                  (print-next)
                  (princ "- ")
                  (print-sort-name (nth x (method-arity src-method))
                                   src-mod)
                  (princ " --> ")
                  (print-sort-name (nth x arity) dst-mod))
                (print-next)
                (princ "- ")
                (print-sort-name (method-coarity src-method) src-mod)
                (princ " --> ")
                (print-sort-name coarity dst-mod)
                (print-next)
                (princ "* operator map")
                (print-next)
                (princ "- source: ")
                (with-in-module (src-mod)
                  (print-chaos-object src-method))
                (print-next)
                (princ "- target: ")
                (with-in-module (dst-mod)
                  (print-chaos-object result))
                (fresh-line))))
          ;;
          result)))))

(defun find-sorts-image* (sorts sort-map mod)
  (mapcar #'(lambda (s) (find-sort-image* s sort-map mod)) sorts))

(defun find-sort-image* (sort sort-map mod)
  (let ((imap (find-if #'(lambda (x) (sort= sort (car x))) sort-map)))
    (if imap
        (cdr imap)
        (find-sort-in mod (sort-id sort)))))

#||
;;; MODEXP-REPLACE-MAPPING view mapping
;;;
(defun modexp-replace-mapping (vm map)
  (if (memq (ast-type vm) '(%view-from '%view-mapping))
      (progn (setf (ast-type vm) '%view-mapping)
             (setf (%view-mapping-map vm) map))
      (break "Internal Error : Misuse of modexp-replace-mapping.")))
||#

;;; EOF
