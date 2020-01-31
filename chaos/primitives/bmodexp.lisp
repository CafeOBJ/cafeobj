;;;-*- Mode:LISP; Package:CHAOS; Base:10; Syntax:Common-lisp -*-
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
#|==============================================================================
                                 System: CHAOS
                               Module: primitives
                               File: bmodexp.lisp
==============================================================================|#
#-:chaos-debug
(declaim (optimize (speed 3) (safety 0) #-GCL (debug 0)))
#+:chaos-debug
(declaim (optimize (speed 1) (safety 3) #-GCL (debug 3)))

;;;*****************************************************************************
;;; MODULE EXPRESSION & VIEW ***************************************************
;;;*****************************************************************************

;;; MODULE EXPRESSION___________________________________________________________
;;; <Modexpr> ::= Identifier              -- simple module name
;;;            |  <Modexpr> * <RenameMap> -- module rename
;;;            |  <Modexpr> + <Modexpr>+  -- module sum
;;;            |  <Modexpr> [ Args ]      -- instantiation
;;;
;;; module MODEXPR {
;;;  signature {
;;;    [ Identifier < ModExpr ]
;;;    [ Idetifier < ViewMap,
;;;      SortMap OpMap <  MapList ]
;;;    op _+_  : ModExpr ModExpr -> ModExpr
;;;    op _*_  : ModExpr MapList -> ModExpr
;;;    op _[_] : ModExpr ViewMap -> ModExpr
;;;    attr _+_ { assoc comm idem l-assoc prec: 3 }
;;;    attr _*_ { l-assoc prec: 2 }
;;;    attr _[_] { l-assoc prec: 1 }
;;;
;;;    op (sort_->_) : Identifier Identifier -> SortMap
;;;    op (op_->_) : Identifier Identifier -> OpMap
;;;    op null-map : -> MapList
;;;    op _,_ : MapList MapList -> MapList
;;;    -- really, _,_ is idempotent : see `axioms' below.
;;;    attr _,_ { assoc comm id: null-map }
;;;
;;;    op (view from_to_{_}) : ModExpr ModExpr MapList -> ViewMap
;;;
;;;    }
;;;
;;;   axioms {
;;;     vars X Y Z : Identifier
;;;     var L : MapList
;;;
;;;     eq sort X -> Y, L, sort X -> Z = L, sort X -> Z  .
;;;     eq op X -> Y, L, op X -> Z = L, op X -> Z .
;;;    }
;;;
;;;  }
;;;
;;; * NOTE *
;;; there are some more forms for modexpr. 

;;;-----------------------------------------------------------------------------
;;; MODULE EXPRESSION
;;; :modexp-value holds internal form of each specific type of module expression.
;;; used only for representing top-level modexpr.
;;; ** NOT USED.
;;;-----------------------------------------------------------------------------
(deftype modexp () '(or simple-string list int-instantiation int-plus int-rename view-struct module))

(defparameter .modexp-keywords. '(%modexp %error %plus %rename %instantiation %view))
                                  
(defun is-modexp? (object)
  (or (stringp object)
      (and (listp object)
           (memq (car object) .modexp-keywords.))))

(defterm modexp (%ast)
  :visible (value)
  :print print-modexp)

;;;-----------------------------------------------------------------------------
;;; RENAME MAPS -- redundant, not used now.
;;; sort/operator/parameter rename maps.
;;;  map : sequence of map (%ren-sort, %ren-op or, %ren-param or %vars)
;;;
(defterm rmap (%ast)
  :visible (map)
  :print print-rename-map)

;;; REN-SORT represents sort mapping.
;;;   maps   : List[pair of source & target]
;;;     - source : sort-ref
;;;     - target : string representing new sort name.
;;;
(defterm ren-sort (%ast)                ; visible sort
  ;; :visible (source target)
  :visible (&rest maps)
  :print print-ren-sort)

(defterm ren-hsort (%ast)               ; hidden sort
  ;; :visible (source target)
  :visible (&rest maps)
  :print print-ren-sort)

;;; REN-OP represents operator mapping.
;;;   maps  : List [ pair of source & target ]
;;;    - source : op-ref.
;;;   -  target : string or list of string representing new operator name.
;;;
(defterm ren-op (%ast)                  ; functional operator
  ;; :visible (source target)
  :visible (&rest maps)
  :print print-ren-op)

(defterm ren-bop (%ast)                 ; behavioural operator
  ;; :visible (source target)
  :visible (&rest maps)
  :print print-ren-op)

;;; VARS
;;;
(defterm vars (%ast)
  :visible (elements)
  :print print-vars-ast)

;;; REN-PARAM
;;; parameter renaming.
;;; source : string 
;;; target : string
;;;
(defterm ren-param (%ast)
  ;; :visible (source target)
  :visible (&rest maps)
  :print print-ren-param)

;;;-----------------------------------------------------------------------------
;;; PLUS : modexp + modexp
;;; module sum.
;;;-----------------------------------------------------------------------------
(defterm + (%ast)
  :name plus
  ;; :visible (plus1 plus2)
  :visible (&rest args)
  :print print-plus-modexp)

;;;-----------------------------------------------------------------------------
;;; RENAME : modexp * { rename_map }
;;;
;;; pre-module-expression level:
;;;   %rename-map ::= { (%ren-sort (a b) (c d) ...) |
;;;                     (%ren-op (x y) (p q) ...)   |
;;;                     (%ren-param (s t) (u v) ...}*)
;;;-----------------------------------------------------------------------------
(defterm * (%ast)
  :name rename
  :visible (module map)
  :print print-rename-modexp)

;;;-----------------------------------------------------------------------------
;;; INSTANTIATION : modexp[args]
;;; an instatiation of parameterized module.
;;;-----------------------------------------------------------------------------
;;; args ::= LIST[ Argname . View]
;;;
(defterm ! (%ast)
  :name instantiation
  :visible (module args)
  :print print-instantiation-modexp)

;;; argument
(defterm !arg (%ast)
  :visible (name view)
  :print print-instantiation-arg)

;;; parse view argument in instantiation
;;; -- NOTE : arg can be a single modexp without any mappings.
;;;           this can be a name of view(string), or arbitrary module expression.
;;;           in this case we construct a special modexp ?name
;;;
(defmacro make-?-name (_modexp_)  `(cons ':?name ,_modexp_))

(defun modexp-is-?name? (modexp)
  (declare (type t modexp)
           (values (or null t)))
  (and (consp modexp) (eq (car modexp) ':?name)))

(defun ?name-name (modexp)
  (cdr modexp))

;;; MODEXP-IS-PARAMETER-THEORY : MODEXP -> BOOL
;;; The form '(string :: modexp ..) is used for representing a module which is a
;;; parameter.
;;;
(defun modexp-is-parameter-theory (e)
  (declare (type t e)
           (values (or null t)))
  (and (consp e)
       (equal "::" (cadr e))))

;;; ****
;;; VIEW
;;; ****

(defterm view (%ast)
  :visible (module                      ; theory module
            target                      ; target module
            map)                        ; mappings
  :print print-view-modexp)

;;; ********************
;;; PREDICATES ON MODEXP________________________________________________________
;;; ********************

;;; MODEXP-IS-ERROR : Modexpr -> Bool
;;; returns t iff the given modexp is error;
;;; the form (:error ....) is used for representing invalid module expressions.
;;;
(defun modexp-is-error (val)
  (declare (type t)
           (values (or null t)))
  (and (consp val) (eq :error (car val))))

;;; MODEXP-IS-SIMPLE-NAME : object -> Bool
;;; returns t iff given object is a 
;;;
(defun modexp-is-simple-name (x)
  (declare (type (or atom modexp) x)
           (values (or null t)))
  (or (stringp x)
      (symbolp x)
      (modexp-is-parameter-theory x)))

;;; *********
;;; MODEXP DB___________________________________________________________________
;;; *********

;;; *MODEXP-VIEW-TABLE* --------------------------------------------------------
;;; alias mapping : canonicalized view expressions -> views.
;;;-----------------------------------------------------------------------------
(declaim (type list *modexp-view-table*))

(defvar *modexp-view-table* nil)

#||
(eval-when (:execute :load-toplevel)
  (setq *modexp-view-table* (make-hash-table :test #'eq)))

(defun find-view-in-env (view)
  (gethash view *modexp-view-table*)
  )

(defun add-view-defn (view value)
  (setf (gethash view *modexp-view-table*) value)
  )

||#

(defun find-view-in-env (view)
  (declare (type modexp view)
           (values (or null t)))
  (find-in-assoc-table *modexp-view-table* view))

(defun add-view-defn (view value)
  (add-to-assoc-table *modexp-view-table* view value))

;;; ********
;;; MODMORHP____________________________________________________________________
;;; ********

;;; IMPLEMENTATION -------------------------------------------------------------
;;; sort : sort mapping, assoc list (source-sort . image-sort).
;;; op   : operator mapping,
;;;        - simple map: renaming modexp also uses this 
;;;          (method :simple-map . method)
;;;        - map to term: general mapping, used by views
;;;          (method :replacement psuedo-variables target-pattern)
;;; module : module replacement, assoc list of (module . module).
;;;
(defstruct (modmorph (:constructor create-modmorph (name sort op module)))
   (name nil :type t)                   ; name of mapping; e.g. name of view or
                                        ; module. (taken from may be more than
                                        ; one view).
   (sort nil :type list)                ; sort map.
   (op nil :type list)                  ; operator map, really is a method map.
   (module nil :type list)              ; module map
   )

;;; TODO : ugly
(defun modmorph-is-rename (map)
  (let ((nm (modmorph-name map)))
    (and (chaos-ast? nm) (eq '%* (ast-type nm)))))

(defmacro  modmorph-assoc-image (_assoc-list _x)
  (once-only (_x)
    ` (or (cdr (assq ,_x ,_assoc-list)) ,_x)))

(defmacro modmorph-assoc-images (_assoc-list _lst)
  ` (mapcar #'(lambda (x)
                (or (cdr (assq x ,_assoc-list))
                    x))
            ,_lst))

;;; ******************************
;;; TOPLEVEL MODEXP INTERNAL FORMS
;;; ******************************
;;; here are internal forms, i.e., modexp with arguments are all evaluated).
;;; these are stored as names of modules, used for reconstructing modexp (internal form)
;;; **********
;;; RENAME MAP__________________________________________________________________
;;; **********

;;; Rename map is used for representing both module renaming and view.
;;; It's just a specification morphism. Applying a map to a signature/module
;;; results to a new signature/module. Theoretically, it is a map (function) 
;;; whose domain is a pair < Sorts, OPS > where Sorts is a set of sort symbols
;;; and OPS is a set of operator names. 

;;; the elements of a map is represented as the followings:
;;; <RENAME-MAP-ELT> ::= (%ren-sort <SortRef> <SortRef>) 
;;;                   |  (%ren-op <OpRef> <OpRef>)
;;;                   |  (%ren-op <Op-Pttern> <Op-Pattern>)
;;;                   |  (%ren-param <ParamName> <ParamName>)
;;;                   |  (%vars (<VarName> ..) <SortRef>)
;;;

;;; EOF
