;;;-*- Mode:LISP; Package:CHAOS; Base:10; Syntax:Common-lisp -*-
;;;
;;; Copyright (c) 2000-2018, Toshimi Sawada. All rights reserved.
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
                              File: modmorph.lisp
==============================================================================|#
#-:chaos-debug
(declaim (optimize (speed 3) (safety 0) #-GCL (debug 0)))
#+:chaos-debug
(declaim (optimize (speed 1) (safety 3) #-GCL (debug 3)))

;;; == DESCRIPTION =============================================================
;;; MODMORPH -- unification of module renaming and view.
;;; RENAME    : sort -> sort, opinfo -> op
;;; VIEW      : sort -> sort, method -> method
;;;                    __ or op -> term for OBJ3 compatible mode, not yet).
;;; PARAMETERIZATION : parameter sub-module -> actual sub-module

;;; (defvar *on-modexp-debug* nil)

;;; ********************
;;; MODMORPH APPLICATION________________________________________________________
;;;     MAIN ROUTINE
;;; ********************

;;;=============================================================================
;;; APPLY-MODMORPH : Name ModMorph Module -> Module
;;; apply a modmorph creating a new module with name `Name'.
;;; - in cases where not mapped, must recreate a new one.
;;;-----------------------------------------------------------------------------

(defun apply-modmorph (name morph mod)
  (let ((newmod (cdr (assq mod (modmorph-module morph)))))
    (if newmod
        ;; given mod already mapped, change its name by given one.
        (setf (module-name newmod) name)
        (progn
          ;; construct new module using given name.
          (setq newmod (or *modmorph-new-module*
                           (!create-module name)))
          ;; register module map.
          (push (cons mod newmod) (modmorph-module morph))))
    ;; apply the morphism
    (with-in-module (newmod)
      (apply-modmorph-internal morph mod newmod))))

;;;=============================================================================
;;; APPLY-MODMORPH* : Name ModMorph Module -> Module
;;; same as above but doesn't rebind *current-module*
;;;-----------------------------------------------------------------------------
(defun apply-modmorph* (nm morph mod)
  (let ((newmod (cdr (assq mod (modmorph-module morph)))))
    (if newmod
        (setf (module-name newmod) nm)
        (progn
          (setq newmod (create-module nm))
          (push (cons mod newmod) (modmorph-module morph))))
    (apply-modmorph-internal morph mod newmod)))

;;;-----------------------------------------------------------------------------
;;; APPLY-MODMORPH-INTERNAL : ModMorph Module Module -> Module
;;; working horse.
;;; apply map to mod filling elements of newmod.
;;;-----------------------------------------------------------------------------
(declaim (special *modmorph-local-vars*))
(defvar *modmorph-local-vars* nil)

(defun apply-modmorph-map-to-op-decl (decl map)
  (declare (ignore map))
  decl)

(defun apply-modmorph-internal (map mod newmod)
  (flet ((inherit-principal-sort (s s-mapped)
           (when (and (null (module-principal-sort newmod))
                      (sort= s (module-principal-sort mod)))
             ;; this will be evaluated later on compilation stage.
             (setf (module-psort-declaration newmod)
               (%psort-decl* s-mapped))
             ;; the following seems redundant, but there are
             ;; some cases the real module compilation is not done
             ;; while evaluating modexprs, and we also want
             ;; psort-declaration for consistency. 
             (setf (module-principal-sort newmod) s-mapped))))
    ;; 
    (when *chaos-verbose* (princ "["))  ; now we begin.
    (when *on-modexp-debug*
      (with-output-simple-msg ()
        (format t "[apply-modmorph] : begin ----------------------------")
        (format t "~&- map = ")
        (print-mapping map)
        (format t "~& - module = ")
        (print-modexp mod)
        (format t "~& - new module = ")
        (print-modexp newmod)))
    ;;
    (let ((amod (assq mod (modmorph-module map))))
      ;; newmod is depends on mod, so we set dependency relation.
      ;; mode :modmorph meas relation is not simple inclusions.
      (add-imported-module newmod :modmorph mod)

      ;; update module map mod->newmod
      (if amod
          (when (null (cdr amod)) (rplacd amod newmod))
        (push (cons mod newmod) (modmorph-module map)))

      ;; this makes temporaly generated module for remaing trash away.
      (when (modmorph-is-rename map)
        (reduce-rename-dummy map mod newmod)
        (print-in-progress ","))

      ;; now finished simple preparation, we begin the real work.
      ;;
      (let ((sortmap (modmorph-sort map))
            (opmap (modmorph-op map))
            (modmap (modmorph-module map))
            (no-error-sort nil))
        
        ;; MAP SUBMODULES -----------------------------------------------------
        ;; the first big job is to incorporate submodules.
        ;; * need to consider sub-module-instantiation
        ;;   also apply mapping; want to memoize appropriately;
        ;;   in some sense must always apply the mapping to sub-objects
        ;; * idea: if sub-module contains parameter as its sub-module then
        ;;   map it (should always be directly there); the other source
        ;;   of information is the name of the module; if is instantiated
        ;;   then can see if the name contains a use of the parameter

        (modmorph-import-submodules mod newmod map mod)
        (print-in-progress ",")
        
        ;; at this point have already got a lot of sorts and operators (etc.)
        ;;   from the incorporated modules

        ;; after have created sub-modules need to "fix" renaming
        (when (modmorph-is-rename map) (fix-sort-renaming map newmod))
        (print-in-progress ",")
        
        ;; now, maps may have been updated, so re-new the local cache.
        (setq sortmap (modmorph-sort map))
        (setq opmap (modmorph-op map))
        (setq modmap (modmorph-module map))

        ;; MAP SORTS, SORT RELATIONS ----------------------------------------
        ;;
        ;; mapping sorts
        (dolist (x (reverse (module-all-sorts mod)))
          (unless (sort-is-for-regularity? x mod)
            ;; reverse because want to preserve the original order
            (let ((sortmapval (assoc x sortmap)))
              (if sortmapval
                  (let ((ims (cdr sortmapval)))
                    (inherit-principal-sort x ims)
                    (unless (memq ims (module-all-sorts newmod))
                      (add-sort-to-module ims newmod))) ; check sort order
                ;; 
                (if (eq mod (sort-module x))
                    (let ((sortim (modmorph-recreate-sort newmod
                                                          modmap
                                                          sortmap
                                                          x))) 
                      (inherit-principal-sort x sortim)
                      (unless (eq x sortim)
                        (push (cons x sortim) sortmap)
                        (setf (modmorph-sort map) sortmap)
                        (setq x sortim))
                      (add-sort-to-module sortim newmod))
                  ;;
                  (let ((modv (assq (sort-module x) modmap)))
                    (if modv
                        (let ((sortim (modmorph-recreate-sort newmod
                                                              modmap
                                                              sortmap
                                                              x)))
                          (inherit-principal-sort x sortim)
                          (unless (eq x sortim)
                            (push (cons x sortim) sortmap)
                            (setf (modmorph-sort map) sortmap)))
                      (inherit-principal-sort x x))))))))
        ;; print progress info
        (if *chaos-verbose*
            (print-in-progress "s")     ; done mapping sorts
          (print-in-progress ","))
        
        ;; sort-relation
        (let ((self-rel (modmorph-recreate-sort-relations newmod
                                                          mod
                                                          modmap
                                                          sortmap
                                                          (module-sort-relations
                                                           newmod))))
          (setf (module-sort-relations newmod)
            (modmorph-merge-sort-relations
             (modmorph-recreate-sort-relations newmod mod modmap sortmap
                                               (module-sort-relations mod)) 
             self-rel)))
        (let ((so (module-sort-order newmod)))
          (dolist (sl (module-sort-relations newmod))
            (add-relation-to-order (copy-sort-relation sl) so))
          ;; we need error sorts
          (when *on-modexp-debug*
            (with-output-msg ()
              (format t " generating error sorts")))
          (generate-err-sorts so)
          (setq no-error-sort t))
        ;; print progress
        (if *chaos-verbose*
            (print-in-progress "<")     ; done mapping sort relations
          (print-in-progress ","))

        ;; MAP OPERATORS ----------------------------------------------------
        ;;
        (when (modmorph-is-rename map)
          ;; operators
          ;; after have created sub-modules need to "fix" renaming for
          ;; operators too.
          (when *on-modexp-debug*
            (with-output-msg ()
              (format t " fixing operator renaming ..")))
          (fix-method-renaming map newmod))
        ;; we postpone error operator declarations by user
        #||
        (let ((new-eop-decls nil))
          (dolist (decl (module-error-op-decl mod))
            (pushnew (apply-modmorph-map-to-op-decl decl map)
                     new-eop-decls
                     :test #'equal))
        (setf (module-error-op-decl newmod) (nreverse new-eop-decls)))
        ||#
        ;; non error operators
        (dolist (opinfo (reverse (module-all-operators mod)))
          ;; want to preserve the original order of operators
          (dolist (method (opinfo-methods opinfo))
            (when (and (not (memq method (module-methods-for-regularity mod)))
                       (not (assq method opmap)))
              (modmorph-recreate-method mod newmod sortmap method))))
        ;; report progress
        (if *chaos-verbose*
            (print-in-progress "o")     ; done mapping operators
          (print-in-progress ","))

        ;; At this point all operators should exist except error operators.
        ;; all of the error sorts & error method should be generated here.
        (modmorph-prepare-for-parsing newmod map no-error-sort)

        ;;  MAP AXIOMS ------------------------------------------------------
        ;; axioms must evaluated when compiling module,
        ;; so we delay their evaluation.
        #||
        ;; equations
        (dolist (e (reverse (module-equations mod)))
          (delay-axiom-importation newmod 
                                   (modmorph-recreate-axiom newmod sortmap opmap modmap e)
                                   newmod))
        ;; transisions
        (dolist (r (reverse (module-rules mod)))
          (delay-axiom-importation newmod
                                   (modmorph-recreate-axiom newmod sortmap opmap modmap r)
        newmod))
        ||#
        (setf (module-equations newmod)
              (append
               (mapcar #'(lambda (r)
                           (when *on-modexp-debug*
                             (with-in-module (mod)
                               (format t "~%* recreating the axiom :")
                               (print-rule r)))
                           (modmorph-recreate-axiom newmod sortmap opmap modmap r))
                       (module-equations mod))
               (module-equations newmod)))
        ;; transitions
        (setf (module-rules newmod)
              (append
               (mapcar #'(lambda (r)
                           (modmorph-recreate-axiom newmod sortmap opmap modmap r))
                       (module-rules mod))
               (module-rules newmod)))

        (if *chaos-verbose*
            (print-in-progress "a")     ; done mapping axioms 
          (print-in-progress ","))
      
        ;; THEOREMS ---------------------------------------------------------
        ;; NO YET
      
        ;; OK we've done, nothing to be done here already.
        ;;
        (when *on-modexp-debug*
          (format t "~%* apply-modmorph: DONE. generated new module ")
          (print-mod-name newmod))
        (if *chaos-verbose*
            (print-in-progress "]")     ; done whole work.
          (print-in-progress ","))
        newmod                          ;the final result
        ))))

(defun modmorph-prepare-for-parsing (mod map no-error-sort)
  (declare (ignore no-error-sort))
  (setup-sem-relations-in mod)
  (make-operator-clusters-in mod)
  (setup-error-operators-in mod)
  (setup-operators-in mod)
  (declare-error-variables-in mod)
  (fix-operator-mapping mod map)
  (dolist (opinfo (module-all-operators mod))
    (modmorph-update-theory mod map opinfo))
  (propagate-attributes mod)
  (update-parse-information mod)
  (mark-module-ready-for-parsing mod))

(defun fix-operator-mapping (mod map)
  (let ((opmap (modmorph-op map))
        (sort-map (modmorph-sort map)))
    (mapc #'(lambda (x)
              (let ((target (cdr x)))
                (cond ((eq (car target) :replacement)
                       (replace-error-method mod (caddr target)
                                             opmap sort-map))
                      ((eq (car target) :simple-error-map)
                       (let ((method (cdr target))
                             (arity nil))
                         (dolist (s (method-arity method))
                           (if (err-sort-p s)
                               (push (find-compatible-err-sort s
                                                               mod
                                                               sort-map)
                                     arity)
                               (push s arity)))
                         (setf (method-arity method) (nreverse arity))
                         (if (err-sort-p (method-coarity method))
                             (setf (method-coarity method)
                                   (find-compatible-err-sort
                                    (method-coarity method)
                                    mod
                                    sort-map)))
                         (setf (car target) :simple-map)))
                      (t nil))))
          opmap)))

(defun modmorph-find-mapped-sorts (module sort-l sortmap)
  (mapcar #'(lambda (x)
              (declare (type sort* x))
              (if (err-sort-p x)
                  (find-compatible-err-sort x module sortmap)
                (or (cdr (assq x sortmap)) x)))
          sort-l))

;;; *******
(defun modmorph-copy-method-attributes (from to)
  (let (sup-strat
        theory
        prec
        memo
        assoc
        constr)
    (let ((from-module (method-module from)))
      (with-in-module (from-module)
        (setf sup-strat (method-supplied-strategy from)
              theory (method-theory from)
              prec (get-method-precedence from)
              memo (method-has-memo from)
              assoc (method-associativity from)
              constr (method-constructor from))))
    (let ((to-module (method-module to)))
      (with-in-module (to-module)
        (setf (method-supplied-strategy to) sup-strat
              (method-precedence to) prec
              (method-has-memo to) memo
              (method-associativity to) assoc
              (method-constructor to) constr)
        (set-method-theory to theory)))))
    
(defun modmorph-find-user-defined-error-method (method module sortmap)
  (let ((arity (modmorph-find-mapped-sorts module
                                           (method-arity method)
                                           sortmap))
        (coarity (car (modmorph-find-mapped-sorts module
                                                  (list (method-coarity method))
                                                  sortmap))))
    
    (multiple-value-bind (op err-method)
        (declare-operator-in-module
         (method-symbol method)
         arity
         coarity
         module
         (method-is-constructor? method) ; constructor?
         (method-is-behavioural method)
         nil
         t)                             ; error method?
      (declare (ignore op))
      (modmorph-copy-method-attributes method err-method)
      err-method)))

(defun modmorph-find-proper-error-method (method opinfos module sortmap)
  (let ((opinfo nil)
        (err-method nil))
    (let ((ar (modmorph-find-mapped-sorts module
                                          (method-arity method)
                                          sortmap))
          (cr (car (modmorph-find-mapped-sorts module
                                               (list (method-coarity method))
                                               sortmap))))
      (declare (type sort* cr))
      (block find-method
        (dolist (oi opinfos)
          (declare (type list oi))
          (dolist (cand (opinfo-methods oi))
            (declare (type method cand))
            ;;-----
            (when (and (sort-list= ar (method-arity cand))
                       (sort= cr (method-coarity cand)))
              (setq opinfo oi)
              (setq err-method cand)
              (return-from find-method nil)))))
        ;;
      (unless opinfo
        ;; failed!....
        ;; this means we need error method
        ;; which are not generated yet. -- really? 
        (let ((arity (mapcar #'(lambda (x)
                                 (declare (type sort* x))
                                 (if (err-sort-p x)
                                     (let ((compo 
                                            (err-sort-components
                                             x)))
                                       (mapcar #'(lambda(y)
                                                   (modmorph-assoc-image
                                                    sortmap
                                                    y))
                                               compo))
                                   (list (modmorph-assoc-image
                                          sortmap
                                          x))))
                             ar))
              (coarity (let ((c cr))
                         (if (err-sort-p c)
                             (let ((compo (err-sort-components c)))
                               (mapcar #'(lambda (s)
                                           (modmorph-assoc-image sortmap s))
                                       compo))
                           (list (modmorph-assoc-image sortmap c)))))
              (so (module-sort-order module)))
          (declare (type sort-order so))
          ;;
          (when (block
                    find-opinfo
                  (dolist (oi opinfos)
                    (declare (type list oi))
                    (let ((mm (opinfo-methods oi)))
                      (dolist (m mm)
                        (declare (type method m))
                        (block try1
                          (let ((xarity (method-arity m))
                                (xcoarity (method-coarity m)))
                            (declare (type list xarity)
                                     (type sort* xcoarity))
                            (dotimes (pos (length xarity))
                              (declare (type fixnum pos))
                              (unless (some #'(lambda (y)
                                                (declare (type sort* y))
                                                (sort<= (the sort*
                                                          (nth pos xarity))
                                                        y
                                                        so))
                                            (nth pos arity))
                                (return-from try1 nil)))
                            (unless (some #'(lambda (y)
                                              (declare (type sort* y))
                                              (sort<= xcoarity y so))
                                          coarity)
                              (return-from try1 nil))
                            (setq opinfo oi)
                            (return-from find-opinfo t)))))))
            ;;
            (setup-error-operator opinfo module)
            (setq err-method (car (opinfo-methods opinfo))))
          (unless err-method
            ;; this means that the original method should be an
            ;; user defined error-method... 
            ;; make sure that really is ...
            (unless (or (some #'(lambda (x)
                                  (declare (type sort* x))
                                  (err-sort-p x))
                              ar)
                        (err-sort-p coarity))
              (with-output-chaos-warning ()
                (format t "well ... could not find proper error method for ")
                (print-chaos-object method))
              (return-from modmorph-find-proper-error-method method))
            ;; we declare err-method
            (multiple-value-bind (o m)
                (declare-operator-in-module
                 (method-symbol method)
                 arity
                 coarity
                 module
                 (method-is-constructor? method) ; constructor?
                 (method-is-behavioural method)
                 nil
                 t)                     ; error method?
              (declare (ignore o))
              (setq err-method m)))     ; end case no err-method
          )))
    ;;
    (when *on-modexp-debug*
      (format t "~%-- finding error method for : ")
      (print-chaos-object method)
      (format t "~%   found : ")
      (print-chaos-object err-method))
    ;;
    err-method))

(defun modmorph-find-error-method (module method opmap sortmap)
  (or (car (memq method (module-error-methods module)))
      (let* ((alen (length (method-arity method)))
             (opinfos nil)
             (name (method-symbol method))
             (mapped? (find-if #'(lambda (x)
                                   (and (method-p (car x))
                                        ;; there is a case built-in constant
                                        ;; is mapped, thus need method-p here.
                                        ;; Wed Mar  3 17:30:33 JST 1999
                                        (equal (method-symbol
                                                (the method (car x)))
                                               name)
                                        (= (the fixnum
                                             (length (method-arity (car x))))
                                           alen)))
                               opmap)))
        (declare (type fixnum alen)
                 (type list opinfos))
        ;;
        (if mapped?
            (progn
              ;; (method :simple-map . method)
              ;; (mehtod :replacement pvars term)
              (when *on-modexp-debug*
                (format t "~%-- finding error method: ")
                (format t "~%   mapped ~s" mapped?))
              (setq name (if (memq (second mapped?)
                                   '(:simple-map :simple-error-map))
                             (method-symbol (the method (cddr mapped?)))
                           (method-symbol (term-head (cadddr mapped?)))))
              (setq opinfos (find-operators-in-module name alen module)))
          ;; mot mapped
          (progn
            (setq opinfos (find-operators-in-module (method-symbol method)
                                                    alen
                                                    module))
            (when *on-modexp-debug*
              (format t "~%-- finding error method: ")
              (format t "~%   not mapped, got infos : ")
              (print-chaos-object opinfos))))
        (cond (opinfos
               (modmorph-find-proper-error-method method
                                                  opinfos
                                                  module
                                                  sortmap))
              (t                        ; this means that the err method is
                                        ; user defined one.
               (modmorph-find-user-defined-error-method method
                                                        module
                                                        sortmap))))))


(defun replace-error-method (mod term op-map sort-map)
  (declare (type module mod)
           (type term term)
           (type list op-map sort-map)
           (values t))
  (if (term-is-application-form? term)
      (let ((head nil))
        (when (or (method-is-error-method (term-head term))
                  (or (sort= (term-sort term) *universal-sort*)
                      (sort= (term-sort term) *huniversal-sort*)))
          (setq head (modmorph-find-error-method mod (term-head term)
                                                 op-map sort-map))
          (when head
            (change-head-operator term head)))
        (dolist (sub (term-subterms term))
          (replace-error-method mod sub op-map sort-map)))
      (if (term-is-variable? term)
          (let ((sort (variable-sort term)))
            (when (err-sort-p sort)
              (let ((new (find-compatible-err-sort sort mod sort-map)))
                (if new
                    (setf (variable-sort term) new)
                    ;; may be error...but
                    nil)))))))

;;; **************
;;; MAP SUBMODULES______________________________________________________________
;;; **************

;;; MODMORPH-MODULE-IS-MAPPED : module-map module -> Bool
;;; returns true iff `module' is mapped in given `module-map'
;;;
(defun modmorph-module-is-mapped (modmap mod) (assq mod modmap))

;;; MODMORPH-SUBMODULE-IS-MAPPED : module-map module -> Bool
;;; returns true iff some submodule of `module' is mapped in given `module-map'.
;;;
(defun modmorph-submodule-is-mapped (modmap mod)
  (some #'(lambda (x)
            (or (modmorph-module-is-mapped modmap (car x))
                (modmorph-submodule-is-mapped modmap (car x))))
        (module-submodules mod)))

;;;=============================================================================
;;; MOD-MORPH-IMPORT-SUBMODULES  : MODULE NEW-MODULE MAP 
;;; import submodules considering mapping.
;;;-----------------------------------------------------------------------------

(defun modmorph-import-submodules (mod newmod map amod)
  (dolist (sbmd (reverse (module-submodules amod)))
    (modmorph-import-submodule mod newmod map (cdr sbmd) (car sbmd))))

;;; MODMORPH-IMPORT-SUBMODULE : MODULE NEW-MOD MAP MODE SUBMODULE
;;;
(defun modmorph-import-submodule (mod newmod map mode submod)
  (let* ((modmap (modmorph-module map))
         (direct-img (assq submod modmap)) ; is it mapped directly?
         (submodule-image nil))
    (when *on-modexp-debug*
      (format t "~%[modmorph-import-submodule]: ")
      (princ " ") (print-modexp newmod) (princ " <== ")
      (print-modexp submod)
      (format t "~& - img:key= ") (print-chaos-object (car direct-img))
      (format t "~& - img:val= ") (print-chaos-object (cdr direct-img)))
    ;; 
    (setq submodule-image
          (if direct-img
              (cond ((or (null (cdr direct-img))
                         (is-dummy-module (cdr direct-img)))
                     ;;case of renaming
                     (when *on-modexp-debug*
                       (format t "~% - case renaming:"))
                     (modmorph-map-submodule map mod submod))
                    (t                  ;associated value is a view in general.
                     (target-of-view-arg (cdr direct-img))))
              (if (modmorph-submodule-is-mapped modmap submod)
                  (modmorph-map-submodule map mod submod)
                  submod)))
    (when *on-modexp-debug*
      (format t "~% -image ")
      (print-modexp submod) (princ " --> ")
      (print-modexp submodule-image))
    ;; 
    (if (eq ':using mode)
        (modmorph-import-submodules mod newmod map submodule-image)
        (import-module newmod mode submodule-image))))

;;;-----------------------------------------------------------------------------
;;; MODMORPH-MAP-SUBMODULE
;;; smod is a sub-module of mod that itself has a mapped sub-module
;;; (i.e., a parameter); thus a sub-instantiation
;;; -- must do appropriate memoization
;;;   to memoize must construct a module expression from the name of
;;;   smod and the name of the relevant parameter (which in general
;;;   may be a view)
;;; constructing the appropriate module expression is rather delicate
;;;  the name of module will be the canonicalized module expression
;;;  not all cases arise; are somewhat restricted.  In this context,
;;;  don't allow a rename that affects the parameter. cases:
;;;  + (act on sub-components); instantiation: check for occurrence
;;;  of module mappped by the mapping, if occurs then rebuild;
;;;  rename (leaf / internal non-bijective) assume mapping not affected
;;;  by the renaming
;;;  for instantiation: occurrence of some parameter must occur
;;;  in some view argument in the instantiation; it will be a canonicalized
;;;  view so the forms of the views will be very regular;
;;;  -- what is being "inserted" is also a view; therefore must
;;;    compose the views
;;;    (apply view to view = composition)
;;;-----------------------------------------------------------------------------

(defun modmorph-map-submodule (map mod smod)
  (let ((parameters (get-module-parameters smod)))
    (cond (parameters   ; was (module-parameters smod)
           (when *on-modexp-debug*
             (format t "~%[modmorph-map-submodule]:")
             (print-modexp smod)
             (format t "~% sub has parameters :")
             (print-chaos-object parameters))
           ;; submdule has parameters,
           ;; checks some of them is mapped or not.
           (let ((mod-map (modmorph-module map))
                 (own-params (mapcar #'(lambda (x) (parameter-theory-module x))
                                     parameters))
                 (args nil))
             (dolist (mmod mod-map)
               (if (memq (car mmod) own-params)
                   (push (%!arg* (car (module-name (car mmod)))
                                 (cdr mmod))
                         args)))
             (let ((new-name (%instantiation* smod  args)))
               ;; * * *
               (apply-modmorph (normalize-modexp new-name) map smod))))
          ;;
          (t (let ((nm (modmorph-construct-name map
                                                ;; (module-name smod)
                                                smod)))
               (let* ((me (normalize-modexp  nm))
                      (val (find-modexp-eval me)))
                 (when *on-modexp-debug*
                   (format t "~%[modmorph-map-submodule]: ")
                   (print-modexp smod)
                   (princ " ==> ")
                   (print-modexp me)
                   (format t "~& - mod = ")
                   (print-modexp mod)
                   (format t "~& - map ")
                   (print-mapping map)
                   (format t "~& - val = ")
                   (print-modexp val))
                 (if val
                     (progn
                       (let ((pair (assq smod (modmorph-module map)))
                             (nmod val))
                         (when *on-modexp-debug*
                           (format t "~& - map pair : ")
                           (format t "~&   key : ")(print-modexp (car pair))
                           (format t "~&   val : ")(print-modexp (cdr pair)))
                         (if pair
                             (rplacd pair val)
                             (push (cons smod val) (modmorph-module map)))
                         (setf (modmorph-module map)
                               (append (modmorph-compute-submodule-mappings
                                        map mod smod)
                                       (modmorph-module map)))
                         nmod))
                     ;;
                     (let ((newmod (apply-modmorph me map smod)))
                       ;; (add-canon-modexp me me)
                       (add-modexp-eval me newmod)
                       (setf (modmorph-module map)
                             (cons (cons smod newmod)
                                   (modmorph-module map)))
                       newmod))))))))

(defvar *modmorph-expanded* nil)

(defun modmorph-construct-name (map smod)
  (cond ((modmorph-is-rename map)
         (let ((s-name (module-name smod)))
           ;; smod can be a direct modexp.
           ;; Wed Mar  3 17:35:05 JST 1999
           (cond ((modexp-is-parameter-theory s-name)
                  (normalize-modexp `(,(parameter-theory-arg-name smod)
                                      "::"
                                      ,(modmorph-construct-name
                                        map
                                        (parameter-module-theory smod))
                                      ,(parameter-module-context smod))))
                 (t (normalize-modexp
                     (%rename* s-name
                               (%rename-map (modmorph-name map))))))))
        (t (let ((*modmorph-expanded* nil))
             (let ((val (modmorph-reconstruct-name map
                                                   (if (module-p smod)
                                                       (module-name smod)
                                                       smod))))
               (if (modexp-is-view val)
                   (let ((val2 (target-of-view-arg val)))
                     (if (module-p val2)
                         (module-name val2)
                         val2))
                   val))))))

;;; want result in canonical form
(defun modmorph-reconstruct-name (map me)
  (when *on-modexp-debug*
    (format t "~%[modmorph-reconstruct-name]:"))
  ;;
  (when (modexp-is-?name? me)
    (when *on-modexp-debug*
      (format t "~% given modexp was ?name? ~a" me))
    (setq me (?name-name me)))
  (when (and (consp me) (equal (second me) "::"))
    (setq me (third me)))
  (cond ((or (module-p me) (stringp me))
         (when *on-modexp-debug*
           (if (stringp me)
               (format t "~% given modexp is string ~s" me)
               (progn (format t "~% given modexp is module object :")
                      (print-chaos-object me))))
         (let ((modval (eval-modexp me)) ; must be global (not argument).
               (modmap (modmorph-module map)))
           (when *on-modexp-debug*
             (format t "~% evaluated value is : ")
             (print-chaos-object modval))
           (let ((im (assq modval modmap)))
             (when *on-modexp-debug*
               (if im
                   (format t "~% evaluated modexp is mapped")
                   (format t "~% evaluated modexp is NOT mapped")))
             (if im 
                 (if (memq modval *modmorph-expanded*)
                     (progn (when *on-modexp-debug*
                              (format t "~% and already expanded."))
                            modval)
                     (progn
                       (when *on-modexp-debug*
                         (format t "~% but not yet expanded, reconstruct the target."))
                       (push modval *modmorph-expanded*)
                       (modmorph-reconstruct-name map (cdr im))))
                 (if (module-p me)
                     (let ((name (module-name me)))
                       (when *on-modexp-debug*
                         (format t "~% modexp was module object."))
                       (if (modexp-is-simple-name name)
                           me
                           (modmorph-reconstruct-name map (module-name me))))
                     (progn (when *on-modexp-debug*
                              (format t "~% modexp was string, returns as is."))
                            me))))))
        ;; PLUS
        ((int-plus-p me)
         (when *on-modexp-debug*
           (format t "~% modexp is internal plus.")
           (pr-int-plus me))
         (make-int-plus :args
                        (mapcar #'(lambda (x) (modmorph-reconstruct-name map x))
                                (int-plus-args me))))
        ((%is-plus me)
         (when *on-modexp-debug*
           (format t "~% modexp is plus, generate new modexp reconstructing args:")
           (print-next)
           (print-modexp me))
         (normalize-modexp
          (%plus* (mapcar #'(lambda (x) (modmorph-reconstruct-name map x))
                          (%plus-args me)))))

        ;; RENAME
        ((int-rename-p me)
         (when *on-modexp-debug*
           (format t "~% modexp is iternal rename.")
           (pr-int-rename me))
         (make-int-rename :module (modmorph-reconstruct-name map
                                                             (int-rename-module me))
                          :sort-maps (int-rename-sort-maps me)
                          :op-maps (int-rename-op-maps me)))
        ((%is-rename me)
         (when *on-modexp-debug*
           (format t "~% modexp is rename, generate new one reconstructing args.")
           (print-next)
           (print-modexp me))
         (normalize-modexp
          (%rename* (modmorph-reconstruct-name map (%rename-module me))
                    (%rename-map me))))

        ;; INSTANTIATION
        ((int-instantiation-p me)
         (when *on-modexp-debug*
           (format t "~% modexp is internal instantiation.")
           (pr-int-instantiation me))
         (let ((modpar (int-instantiation-module me)))
           (make-int-instantiation
            :module (modmorph-reconstruct-name map modpar)
            :args (let ((res nil))
                    (dolist (arg (int-instantiation-args me)
                             (nreverse res))
                      (push (modmorph-reconstruct-view-arg
                             (%!arg-name arg)
                             (%!arg-view arg)
                             map
                             modpar)
                            res))))))
        ;;
        ((%is-instantiation me)
         (when *on-modexp-debug*
           (format t "~% modexp is instantiation, generate new one....")
           (print-next)
           (print-modexp me))
         (let* ((modpar (%instantiation-module me))
                (modparnm (if (module-p modpar)
                              (module-name modpar)
                              modpar)))
           (%instantiation* (modmorph-reconstruct-name map modparnm)
                            (let ((res nil))
                              (dolist (arg (%instantiation-args me))
                                (push (modmorph-reconstruct-view-arg
                                       (%!arg-name arg) ; name
                                       (%!arg-view arg) ; view
                                       map
                                       modpar)
                                      res))
                              (nreverse res)))))

        ;; VIEW
        ((view-p me)
         (when *on-modexp-debug*
           (format t "~% modexp is view structure, create new one.")
           (print-next)
           (print-modexp me))
         (let ((view (view-struct* (view-struct-name me))))
           (setf (view-struct-src view) (view-struct-src me))
           (setf (view-struct-target view)
                 (modmorph-reconstruct-name map (view-struct-target me)))
           (setf (view-struct-sort-maps view) (view-struct-sort-maps me)
                 (view-struct-op-maps view) (view-struct-op-maps me))
           (setf (view-decl-form view) (view-decl-form me))
           view))
        ;;
        (t (break "modmorph-reconstruct-name: missing case"))))

(defun target-of-view-arg (vw)
  (when (modexp-is-?name? vw)
    (setq vw (?name-name vw)))
  (cond ((stringp vw) vw)
        ((module-p vw) vw)
        ((view-p vw) (view-target vw))
        ((%is-view vw) (%view-target vw))
        (t (break "target-of-view-arg: unknown view argument"))))

(eval-when (:execute :compile-toplevel :load-toplevel)
  (declaim (type fixnum *anon-view-name*))
  (defvar *x-anon-view-name* 0)
  (defun make-anon-view-name ()
    (intern (format nil "ANON-VIEW-~D" (incf *x-anon-view-name*))))
)

(defun modmorph-reconstruct-view-arg (arg-name vw map modpar)
  (declare (ignore modpar))
  (unless (view-p vw)
    (with-output-panic-message ()
      (format t "recostructing view illegual view:")
      (print-chaos-object vw)
      (chaos-error 'panic)))
  (let* ((tgt (target-of-view-arg vw))
         (modmap (modmorph-module map))
         (val (assq tgt modmap))
         (mod (view-src vw)))
    (when *on-modexp-debug*
      (format t "~%[reconstruct-view-arg]:arg-name=~a " arg-name)
      (print-next)
      (print-chaos-object vw)
      (force-output))
    (let ((actual (or (cdr val) tgt)))
      (let ((tmod (if (module-p actual)
                      actual
                      (target-of-view-arg actual)))
            (view (view-struct* (make-anon-view-name))))
        (when *on-modexp-debug*
          (format t "~%- src = ")(print-chaos-object mod)
          (format t "~&- tgt = ")(print-chaos-object tmod)
          (unless tmod (break "Oh my God!")))
        (setf (view-src view) mod)
        (setf (view-target view) tmod)
        (setf (view-sort-maps view)
              (modmorph-reconstruct-view-sort-mapping
               tmod
               map
               (view-sort-maps vw)))
        (setf (view-op-maps view)
              (modmorph-reconstruct-view-op-mapping
               tmod
               map
               (view-op-maps vw)))
        (when *on-modexp-debug*
          (format t "~%*result view=")
          (print-chaos-object view))
        (%!arg* arg-name view)))))

(defun modmorph-reconstruct-view-sort-mapping (mod map s-maps)
  (declare (ignore mod))
  (let ((res nil)
        (modmorph-sort-map (modmorph-sort map)))
    (dolist (s-map s-maps (nreverse res))
      (push (cons (car s-map)
                  (modmorph-assoc-image modmorph-sort-map
                                        (cdr s-map)))
            res))))

(defun modmorph-reconstruct-view-op-mapping (mod map o-maps)
  (let ((res nil)
        (modmorph-op-map (modmorph-op map)))
    (dolist (o-map o-maps (nreverse res))
      (push (list (car o-map)
                  (modmorph-apply-op-map-2 mod
                                           map
                                           modmorph-op-map
                                           (cadr o-map)))
            res))))

;;; op-mapping ::= (:simple . method)
;;;              | (:replacement List[psuedo var] term)
;;;
(defun apply-op-mapping-2 (module map op-mapping term)
  (if (eq ':simple-map (car op-mapping))
      (make-term-check-op-with-sort-check (cdr op-mapping)
                                          (term-subterms term)
                                          module)
      (with-in-module (module)
        (mapping-image-2 map (term-subterms term) (caddr op-mapping)))))

(defun modmorph-apply-op-map-2 (module map op_map term)
  (let ((val (assoc (term-head term) op_map)))
    (if val
        (apply-op-mapping-2 module map (cdr val) term)
        (let* ((op (term-head term)) 
               (om (method-module op))
               (as (assoc om (modmorph-module map))))
          (if (and as (cdr as) (not (eq (cdr as) om)))
              (with-in-module (module)
                (mapping-image-2 map (term-subterms term) term))
              term)))))


;;; MODMORPH-COMPUTE-SUBMODULE-MAPPINGS:
;;;
(defun modmorph-compute-submodule-mappings (map mod smod)
  (when *on-modexp-debug*
    (format t "~%[modmorph-compute-submodule-mappings]:")
    (format t "~& - map = ") (print-mapping map)
    (format t "~& - mod = ") (print-modexp mod)
    (format t "~& - smod = ") (print-modexp smod))
  (let ((res nil)
        (modmap (modmorph-module map)))
    (dolist (smp (module-submodules smod))
      (let ((sm (car smp)))
        (cond ((and (not (eq ':using (cdr smp)))
                    (modmorph-submodule-is-mapped modmap sm))
               (when *on-modexp-debug*
                 (format t "~& - sm = ") (print-modexp sm)
                 (format t " is mapped."))
               (setq res
                     (cons (cons sm
                                 (eval-modexp (modmorph-construct-name
                                               map
                                               ;; (module-name sm)
                                               sm)))
                           (append (modmorph-compute-submodule-mappings map mod sm)
                                   res))))
              ;;
              (t (let ((aval (assq sm modmap)))
                   (when *on-modexp-debug*
                     (format t "~& - aval(img) = ") (print-modexp (cdr aval)))
                   (when (and aval
                              (is-dummy-module (cdr aval)))
                     (let ((newm (eval-modexp 
                                  (modmorph-construct-name map
                                                           ;; (module-name sm)
                                                           sm))))
                       #||
                       (push (cons (cdr aval) newm)
                             (modmorph-module map))
                       ||#
                       (rplacd aval newm))))))))
    res))

;;; ******************
;;; RECREATING OBJECTS__________________________________________________________
;;; ******************

;;; SORTS/SORT RELATIONS

;;;-----------------------------------------------------------------------------
;;; MODMORPH-RECREATE-SORT : Module Modmap SortMap Sort -> Sort
;;;-----------------------------------------------------------------------------

(defun modmorph-recreate-sort (mod modmap sortmap sort)
  (let ((sort-name (sort-id sort))
        (smod (sort-module sort)))
    (let* ((mmod (cdr (assq smod modmap)))
           (themod (if (and mmod (module-p mmod)) mmod mod))
           (asort (find sort-name (module-all-sorts mod)
                        :test #'(lambda (n s)
                                  (and (equal n (sort-id s))
                                       (eq themod (sort-module s)))))))
      (when *on-modexp-debug*
        (format t "~%[modmorph-recreate-sort]:")
        (format t "~&-- modmap = ")
        (dolist (i modmap)
          (print-next)
          (print-modexp (car i)) (princ "-->")
          (print-modexp (cdr i)) (princ " "))
        (format t "~&-- mod = ") (print-modexp mod)
        (format t "~&-- thmod = ") (print-modexp themod)
        (format t "~&-- sort-name = ~a" (string sort-name))
        (format t "~&-- smod      = ") (print-modexp smod))
      ;;
      (if asort
          asort
          (let ((newsort (!recreate-sort themod sort)))
            ;;
            (when *on-modexp-debug*
              (format t "~%* generated the new one!!!"))
            (push (cons sort newsort) sortmap)
            newsort)
          ))))

;;;-----------------------------------------------------------------------------
;;; MODMORPH-RECREATE-SORT-RELATIONS
;;;-----------------------------------------------------------------------------

(defun modmorph-recreate-sort-relations (module oldmod modmap sortmap sort-relations)
  (macrolet ((reduce-sort-set (x)
               ` (let (($$res nil))
                   (dolist (e ,x) (unless (memq e $$res) (push e $$res)))
                   (nreverse $$res))))
    (let ((res nil))
      (dolist (rel sort-relations)
        (let ((rel (elim-sys-sorts-from-relation rel)))
          (when rel (push rel res))))
      (mapcar #'(lambda (sl)
                  (let ((srt (modmorph-sort-image-create
                              module oldmod modmap sortmap
                              (sort-relation-sort sl))) 
                      (subs (reduce-sort-set
                             (modmorph-sorts-image-create module oldmod modmap
                                                          sortmap (_subsorts
                                                                   sl))))  
                      (sups (reduce-sort-set
                             (modmorph-sorts-image-create module oldmod modmap
                                                          sortmap (_supersorts
                                                                   sl))))) 
                  (make-sort-relation srt subs sups)))
              res))))

;; *NOTE* assume all of the system generated sorts are eliminated.

(defun modmorph-merge-sort-relations (sl1 sl2)
  (dolist (x sl1)
    (let ((rel (assq (sort-relation-sort x) sl2)))
      (if rel
          (progn
            (setf (_subsorts rel) (union (_subsorts x) (_subsorts rel)
                                         :test #'eq)) 
            (setf (_supersorts rel) (union (_supersorts x) (_supersorts rel)
                                           :test #'eq))) 
          (push x sl2))))
  sl2)
        
;;;
;;;
(defun modmorph-sort-image-create (module oldmod modmap sortmap sort)
  (let ((s1 (modmorph-assoc-image sortmap sort)))
    (if (not (eq s1 sort))
        s1
        (if (is-dummy-module (sort-module sort))
            (let* ((mod (sort-module sort))
                   (info (get-rename-info mod))
                   (oldmod (car info))
                   (modim (cdr (assq oldmod modmap))))
              (if modim
                  (let ((val (let ((asrt
                                    (modmorph-find-sort-in modim (sort-id sort))))
                               (if asrt asrt
                                   (if (or (eq sort *universal-sort*)
                                           (eq sort *huniversal-sort*)
                                           (eq sort *bool-sort*)
                                           (eq sort *sort-error*))
                                       sort
                                       nil)))))
                    (if val
                        val
                        (progn
                          (setf (sort-module sort) modim)
                          (add-sort-to-module sort modim)
                          sort)))
                  sort))
            (if (not (eq oldmod (sort-module sort)))
                sort
                (let ((newsort (modmorph-recreate-sort module
                                                       modmap
                                                       sortmap
                                                       sort)))
                  (add-sort-to-module newsort module)
                  newsort))))))

(defun modmorph-sorts-image-create (module oldmod modmap sortmap sortlist)
  (let ((img (mapcar #'(lambda (x) (modmorph-sort-image-create module
                                                               oldmod
                                                               modmap
                                                               sortmap
                                                               x))
                     sortlist)))
    img))

;;; sort should already exist
;;;
(defun modmorph-sort-image (module sortmap sort)
  (let ((s1 (modmorph-assoc-image sortmap sort)))
    (if (or (memq s1 (module-all-sorts module))
            (memq s1 (module-error-sorts module)))
        s1
        (let ((val (if (err-sort-p sort)
                       (find-compatible-err-sort sort module sortmap)
                       (find-sort-in module (sort-id s1)))))
          ;; (break)
          (if val
              val
              (if (or (eq sort *universal-sort*)
                      (eq sort *huniversal-sort*)
                      (eq sort *bool-sort*)
                      (eq sort *sort-error*))
                  sort
                  (unless (err-sort-p s1)
                    (with-output-chaos-warning ()
                      (format t "image sort ~a not found in module "
                              (string (sort-id s1)))
                      (print-chaos-object module)
                      ;; (break)
                      (return-from modmorph-sort-image nil)))))))))

(defun modmorph-sorts-image (module sortmap sortlist)
  (mapcar #'(lambda (x) (modmorph-sort-image module sortmap x))
          sortlist))

;;; OPERATORS

;;;-----------------------------------------------------------------------------
;;; MODMORPH-RECREATE-METHOD : OldMOD Module Sort-Mapping Method -> Void
;;;-----------------------------------------------------------------------------

(defun modmorph-recreate-method (oldmodule module sortmap method)
  (when (or (not (method-is-error-method method))
            (method-is-user-defined-error-method method))
    (let ((op-symbol (method-symbol method))
          (arity (modmorph-sorts-image module
                                       sortmap
                                       (method-arity method)))
          (coarity (modmorph-sort-image module
                                        sortmap
                                        (method-coarity method))))
      (let ((val (find-method-in module op-symbol arity coarity)))
        (when *on-modexp-debug*
          (when val
            (format t "~%[modmorph-recreate-method] :")
            (format t "~&-method image is already in module ")
            (print-chaos-object method)))
        (if val
            (modmorph-recreate-method-aux-2 oldmodule module sortmap val)
          (modmorph-recreate-method-aux-1 oldmodule
                                          module
                                          method
                                          op-symbol
                                          arity
                                          coarity
                                          sortmap))))))

(defun modmorph-recreate-method-aux-1 (oldmodule module
                                                 method
                                                 op-symbol
                                                 arity
                                                 coarity
                                                 sort-map)
  (recreate-method oldmodule method module op-symbol arity coarity sort-map))

(defun modmorph-recreate-method-aux-2 (oldmodule module sortmap method)
  (declare (ignore sortmap))
  (when (get-method-info method (module-opinfo-table oldmodule))
    (transfer-operator-theory method module oldmodule)))

(defun modmorph-update-theory (mod map opinfo)
  (let ((minfo (module-opinfo-table mod)))
    (dolist (method (opinfo-methods opinfo))
      (let ((thy (method-theory method minfo)))
        (when thy
          (setf (method-theory method minfo)
                (cond ((theory-contains-identity thy)
                       (let ((zero (theory-zero thy)))
                         (if zero
                             (progn
                               (theory-make
                                (theory-info thy)
                                (let ((srtmap (modmorph-sort map))
                                      (opmap (modmorph-op map))
                                      (modmap (modmorph-module map))
                                      (idinf (if (eq '%to-rename
                                                     (car zero))
                                                 (cdr zero) 
                                                 zero)))
                                  (cons (modmorph-recreate-term mod
                                                                srtmap
                                                                opmap
                                                                modmap
                                                                (car idinf))
                                        (cdr idinf)))))
                             thy)))
                      (t thy)))
          (compute-method-theory-info-for-matching method minfo)))                              ; dolist
      )))

;;; TERMS

;;;-----------------------------------------------------------------------------
;;; MODMORPH-RECREATE-TERM :
;;;   Module Sort-Mapping Op-Mapping Mod-Mapping Term -> Term
;;;-----------------------------------------------------------------------------

;;; *VIEW-FROM????
(defun modmorph-recreate-term (module sortmap opmap modmap term)
  (cond ((term-is-an-error term) term)
        ((term-is-builtin-constant? term)
         (make-bconst-term (modmorph-sort-image module
                                                sortmap
                                                (term-sort term))
                           (term-builtin-value term)))
        ((term-is-lisp-form? term) term)
        ((term-is-variable? term)
         (when *on-modexp-debug*
           (format t "~%[modmorph-recreate-term] finding variable ~a of sort ~a"
                   (variable-name term)
                   (sort-name (variable-sort term))))
         ;; the operator should always be found
         (let ((var-name (variable-name term)))
           (let ((img-sort (modmorph-sort-image module
                                                sortmap
                                                (variable-sort term))))
             (let ((val2 (find-if #'(lambda (x)
                                      (and (equal var-name (variable-name x))
                                           (sort= img-sort (variable-sort x))))
                                  *modmorph-local-vars*)))
               (if val2
                   (progn (when *on-modexp-debug*
                            (format t "~% variable found."))
                          val2)
                   (let ((new-var (make-variable-term img-sort var-name)))
                     (when *on-modexp-debug*
                       (format t "~% variable not found in *modmorph-local-vars*"))
                     (push new-var *modmorph-local-vars*)
                     new-var))))))
        (t (let ((head (term-head term))
                 (new-head nil))
             ;; look in the mapping
             (when *on-modexp-debug*
               (format t "~%[modmorph-recreate-term]: looking for image of ")
               (print-method head))
             ;;
             (let ((val (assoc head opmap)))
               (if val
                   (progn
                     (when *on-modexp-debug*
                       (format t "~% found the image in map.")
                       (print-chaos-object (cddr val)))
                     (if (eq :replacement (second val))
                         (progn (setq term (apply-op-mapping module
                                                             (cdr val)
                                                             term))
                                (setq new-head (term-head term)))
                         (setq new-head (cddr val))))
                   (when *on-modexp-debug*
                     (format t "~% not mapped (image not found in map.)")))
               (unless new-head
                 ;; method is not mapped
                 (if (method-is-error-method head)
                     (setq new-head
                           (modmorph-find-error-method module
                                                       head
                                                       opmap
                                                       sortmap))
                     (let ((aval (assoc (method-module head) modmap)))
                       (setq new-head
                             (if (not aval)
                                 head
                                 (let ((lookmod
                                        (if (module-p (cdr aval))
                                            (cdr aval)
                                            (if (view-p (cdr aval))
                                                (view-target (cdr aval))
                                                (cdr aval)))))
                                   (find-method-in
                                    lookmod
                                    (method-symbol head)
                                    (modmorph-sorts-image lookmod
                                                          sortmap
                                                          (method-arity head))
                                    (modmorph-sort-image lookmod
                                                         sortmap
                                                         (method-coarity head)))))))))
               ;;
               (unless new-head
                 (with-output-chaos-error ('no-such-operator)
                   (princ "mapping image of operator: ")
                   (with-in-module ((method-module head))
                     (print-method-internal head))
                   (print-next)
                   (princ "of module ")
                   (print-chaos-object (method-module head))
                   (print-next)
                   (princ "was not found in the module ")
                   (print-chaos-object module)
                   ))
               (when *on-modexp-debug*
                 (format t "~% new op: ")
                 (print-method-internal new-head))
               ;;
               (if (term-is-builtin-constant? term)
                   term
                   (make-term-check-op-with-sort-check
                    new-head
                    (mapcar #'(lambda (tm)
                                (modmorph-recreate-term module
                                                        sortmap
                                                        opmap
                                                        modmap
                                                        tm))
                            (term-subterms term))
                    module)))))))

;;; AXIOMS

;;;-----------------------------------------------------------------------------
;;; MODMORPH-RECREATE-AXIOM :
;;;        Module Sort-Mapping Operator-Mapping Mod-Mapping Axiom -> Axiom
;;;-----------------------------------------------------------------------------

(defun modmorph-recreate-axiom (module sortmap opmap modmap ax)
  (with-in-module (module)
    (let ((*modmorph-local-vars* nil))
      (make-rule :lhs (modmorph-recreate-term module
                                              sortmap
                                              opmap
                                              modmap
                                              (axiom-lhs ax))
                 :rhs (modmorph-recreate-term module
                                              sortmap
                                              opmap
                                              modmap
                                              (axiom-rhs ax))
                 :condition (if (is-true? (axiom-condition ax))
                                *bool-true*
                                (modmorph-recreate-term 
                                 module
                                 sortmap
                                 opmap
                                 modmap
                                 (axiom-condition ax)))
                 :labels (axiom-labels ax)
                 :behavioural (axiom-is-behavioural ax)
                 :type (axiom-type ax)
                 :kind (axiom-kind ax)
                 :non-exec (axiom-non-exec ax)
                 :meta-and-or (axiom-meta-and-or ax)))))

;;; *******************
;;; MISC MODMORPH UTILS_________________________________________________________
;;; *******************

;;;-----------------------------------------------------------------------------
;;; modmorph-merge : Mapping Mapping -> Mapping
;;;-----------------------------------------------------------------------------

(defun modmorph-merge (m1 m2 &optional (warn t))
  (let ((nm1 (modmorph-name m1))
        (nm2 (modmorph-name m2)))
    (create-modmorph
     ;; name will need to be used for memoization
     ;; the assumption here is that basic mappings have names like:
     ;;     (map th vw)
     ;; and that other names are create by this routine
     (append (if (atom (car nm1)) (list nm1) nm1)
             (if (atom (car nm2)) (list nm2) nm2))
     (modmorph-merge-assoc (modmorph-sort m1) (modmorph-sort m2) warn)
     (modmorph-merge-op-assoc (modmorph-op m1) (modmorph-op m2) warn)
     (modmorph-merge-assoc (modmorph-module m1) (modmorph-module m2) warn))))

(defun modmorph-merge-assoc (a1 a2 &optional warn)
  (let ((res a2))
    (dolist (m a1)
      (let ((im (assq (car m) a2)))
        (if (and im
                 (not (eq (car m) (cdr m))))
            (progn
              (unless (eq (cdr im) (cdr m))
                (when warn
                  (with-output-chaos-warning ()
                    (princ "instantiating module, ")
                    (print-next)
                    (princ "combined view has inconsistent mappings for: ")
                    (let ((*print-indent* (+ *print-indent* 2)))
                      (print-next)
                      (print-chaos-object (car m)))
                    (print-next)
                    (princ "target images are: ")
                    (let ((*print-indent* (+ *print-indent* 2)))
                      (print-next)
                      (print-chaos-object (cdr m))
                      (print-next)
                      (print-chaos-object (cdr im)))
                    ))))
            (push m res))))
    res))

(defun modmorph-op-map-is-ident (map)
  (if (eq :simple-map (second map))
      ;; map := (method :simple-map method)
      (eq (first map) (third map))
      ;; map := (term :replacement vars term)
      (eq (first map)
          (term-head (fourth map)))))

(defun modmorph-merge-op-assoc (a1 a2 &optional warn)
  (let ((res a2))
    (dolist (m a1)
      (let ((im (assq (car m) a2)))
        (if (and im
                 (not (modmorph-op-map-is-ident m)))
            (progn
              (unless (modmorph-same-op-image (cdr m) (cdr im))
                (when warn
                  (with-output-chaos-warning ()
                    (princ "instantiating module,")
                    (print-next)
                    (princ "combined view has inconsistent mappings for operator: ")
                    (let ((*print-indent* (+ *print-indent* 2)))
                      (print-next)
                      (print-chaos-object (car m)))
                    (print-next)
                    (princ "images are: ")
                    (let ((*print-indent* (+ *print-indent* 2)))
                      (if (eq (cadr m) :replacement)
                          (progn
                            (print-next)
                            (print-chaos-object (cadddr m))
                            (print-next)
                            (print-chaos-object (cadddr im)))
                          (progn
                            (print-next)
                            (print-chaos-object (caddr m))
                            (print-next)
                            (print-chaos-object (caddr m)))))
                    ))))
            (push m res))))
    res))

;;  im1 & im2 are of the form 
;;;   (:simple-map . method) -- or --
;;;   (:replacement psuedo-vars dst-term)
;;;
(defun modmorph-same-op-image (im1 im2)
  (if (and (consp im1) (eq :simple-map (car im1)))
      (or (eq (cdr im1) (cdr im2))
          (and (equal (method-name (cdr im1))
                      (method-name (cdr im2)))
               (sort= (method-coarity (cdr im1))
                      *sort-id-sort*)))
      ;;
      (if (and (consp im1) (eq :replacement (car im1)))
          (if (sort= (term-sort (caddr im1)) *sort-id-sort*)
              (and (sort= (term-sort (caddr im2)) *sort-id-sort*)
                   (equal (method-name (term-head (caddr im1)))
                          (method-name (term-head (caddr im2)))))
              (term-equational-equal (caddr im1) (caddr im2))))))

;;; op modmorph-find-sort-in : Module Sort-Name -> Sort
;;;
(defun modmorph-find-sort-in (module sort-name)
  (or (find sort-name (module-all-sorts module)
            :test #'(lambda (n s)
                      (and (equal n (sort-id s))
                           (eq module (sort-module s)))))
      nil))

;;;
;;;
(defun modmorph-find-operator-named-in (module op-symbol)
  (let ((res1 (find-if  #'(lambda (opinfo)
                            (let ((op (opinfo-operator opinfo)))
                              (or (equal op-symbol (operator-symbol op))
                                  (and (eq module (operator-module op))
                                       (if (atom op-symbol)
                                           (equal op-symbol (car (operator-symbol op)))
                                           (and (null (cdr op-symbol))
                                                (equal (car op-symbol)
                                                       (car (operator-symbol op)))))))))
                        (module-all-operators module))))
    (or res1
        (dolist (srt (module-all-sorts module) nil)
          (if (sort-is-builtin srt)
              (let ((res (find-builtin-method-in module srt op-symbol)))
                (if res (return res)))))
        )))

;;; APPLY-OP-MAPPING : module op-mapping term -> term
;;;
;;; op-mapping ::= (:simple-map . method)
;;;              | (:replacement List[psuedo-variable] dst-pattern)
;;;
(defun apply-op-mapping (module op-mapping term)
  (if (eq :simple-map (car op-mapping))
      (make-term-check-op-with-sort-check (cdr op-mapping)
                                          (term-subterms term))
      (mapping-image (term-subterms term) (caddr op-mapping) module)
                                        ;caddr = dst-pattern
      ))

;;; APPLY-OP-MAP
;;;
(defun apply-op-map (module op-map term)
  (let ((val (assoc (term-head term) op-map)))
    (if val
        (apply-op-mapping module (cdr val) term)
        term)))

;;; MAPPING-IMAGE:
;;; variables occuring in term are assumed to have numbers as names
;;; that are indices into term_list; var "1" get replaced by (nth 1 term_list)
;;; indices are 0-origin
;;;
(defvar .mapping-debug. nil)

(defun mapping-image (term-list term &optional (module (get-context-module)))
  (when .mapping-debug.
    (format t "~%[mapping-image] term = ")
    (print-chaos-object term)
    (format t "~% term-list = ")
    (print-chaos-object term-list))
  (cond ((term-is-variable? term)
         (let ((nm (variable-name term)))
           (if (integerp nm) (nth nm term-list)
               (with-output-panic-message ()
                 (princ "mapping-image: illegal variable")
                 (print-next)
                 (princ "var: ") (print-chaos-object term)
                 (chaos-error 'panic)))))
        ((term-is-constant? term) term)
        (t (make-term-check-op-with-sort-check
            (term-head term)
            (mapcar #'(lambda (st) (mapping-image term-list st))
                    (term-subterms term))
            module))))

(defun mapping-image-2 (map term_list term)
  (cond  ((term-is-variable? term)
          (let ((nm (variable-name term)))
            (if (integerp nm) (nth nm term_list)
                (with-output-panic-message ()
                  (princ "mapping-image2: illegal variable")
                  (print-next)
                  (princ "var: ") (print-chaos-object term)
                  (chaos-error 'panic)))))
         ((term-is-constant? term) term)
         (t (let* ((op (term-head term))
                   (om (method-module op))
                   (as (or (cdr (assoc om (modmorph-module map)))
                           om)))
              (when (and (not (eq as om))
                         (module-p as))
                (setq op (find-method-in as ; was (cdr as).
                                         (method-symbol op)
                                         (modmorph-sorts-image as ; (cdr as)
                                                               (modmorph-sort map)
                                                               (method-arity op))
                                         (modmorph-sort-image as ; (cdr as)
                                                              (modmorph-sort map)
                                                              (method-coarity op)))))
              (unless op
                (with-output-panic-message ()
                  (format t "mapping term image, could not find operator image:")
                  (print-method (term-head term))
                  (chaos-error 'panic)))
              (make-term-check-op-with-sort-check op
                                                  (mapcar #'(lambda (st)
                                                              (mapping-image-2
                                                               map term_list
                                                               st))
                                                          (term-subterms term))
                                                  (if (module-p as)
                                                      as
                                                      om))))))

;;;
(defun view-get-image-of-axioms (view)
  (let* ((source (view-source view))
         (target (view-target view))
         (morph (convert-view-to-modmorph source
                                          view)))
    (modmorph-get-image-of-axioms morph source target)))
        
(defun modmorph-get-image-of-axioms (morph source target)
  (let ((sort-map (modmorph-sort morph))
        (op-map (modmorph-op morph))
        (mod-map (modmorph-module morph))
        (all-axioms (get-module-axioms target))
        (axs nil))
    (dolist (ax (get-module-axioms source))
      (let ((ax-image (modmorph-recreate-axiom target sort-map op-map mod-map ax)))
        (unless (member ax-image all-axioms :test #'rule-is-similar?)
          (push ax-image axs))))
    (nreverse axs)))

;;; EOF
