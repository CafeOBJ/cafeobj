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
                               Module: construct
                                 File: cr.lisp
==============================================================================|#
#-:chaos-debug
(declaim (optimize (speed 3) (safety 0) #-GCL (debug 0)))
#+:chaos-debug
(declaim (optimize (speed 1) (safety 3) #-GCL (debug 3)))

#|| * TODO * -------------------------------------------------------------------
- type check for attribute values as creating instances.
||#

;;; Ast of class/record declaration --------------------------------------------
;;; ( type
;;;   "name"
;;;   <supers>
;;;   <attributes>
;;;  )
;;;
;;; an example:
;;;    (%class-decl
;;;         "Nfa'"
;;;         ((%super (%sort "Lts" nil)
;;;                  ((%attr-rename "current" "ima")
;;;                   (%attr-rename "rules" "trans")))
;;;          (%super (%sort "Aho" nil) nil))
;;;         ((%slot "current" (%sort "Int" nil) nil)
;;;          (%slot "aho" (%sort "Nat" nil) ("1" "+" "2"))))
;;;

;;; DECLARE-CR-SORT : module name supers type
;;;   module : module in which the sort will be declared
;;;   name   : name of the sort, string.
;;;   supers : list of super sort reference.
;;;   type   : should be class-sort or record-sort.
;;; 
;;; References to super sorts are resolved, rename maps in the input are still
;;; remain.  
;;; Returns the list of super-reference of the form :
;;; ( SuperSort AttirbuteRenameMap ) 
;;;
(defun sort-to-id-sort (sort mod)
  (declare (ignore mod)
           (type sort-struct sort)
           (type module mod)
           (values sort-struct))
  (if (crsort-p sort)
      (method-coarity (crsort-id-method sort))
      (error "Internal error : sort-to-id-sort gets non r/c sort ~s"
             (sort-id sort))))

(defun declare-cr-sort (module name supers type &optional hidden)
  (declare (type module module)
           (type t name)
           (type list supers)
           (type symbol type)
           (type (or null t) hidden)
           (values sort-struct t))
  (with-in-module (module)
    (let ((sort (or (find-sort-in module name)
                    (declare-sort-in-module (intern name) module type hidden)))
          spr
          (super-refs nil))
      (declare (type sort-struct sort))
      ;; define sort relation with super classes
      ;; check if supers really exist.
      (dolist (sup supers)
        (if (setq spr (find-sort-in module (%super-sort sup)))
            (progn
              (when hidden
                (unless (sort-is-hidden spr)
                  (with-output-chaos-error ('invalid-hidden-sort)
                    (format t "you cannot declare subsort relation between visible sort and hidden sort,~% the super sort ")
                    (print-sort-name spr)
                    (print-next)
                    (format t " is visible, but should be hidden in this context.")
                    )))
              (push (list spr (%super-renames sup)) super-refs))
            (with-output-chaos-error ('no-such-sort)
              (format t "no such sort ,")
              (print-ast sup)
              (print-next)
              (format t "super ")
              (print-ast sup)
              (print-next)
              (format t " is ignored.")
              )))
      (if super-refs
          (declare-subsort-in-module (list (list* sort
                                                  ':<
                                                  (mapcar #'car super-refs))))
          (declare-subsort-in-module (list (list sort ':< (if (eq type 'class-sort)
                                                              *object-sort*
                                                              *record-instance-sort*
                                                              )))))
      (values sort super-refs))))


;;; PROCESS-SLOT-DECLARATION : module supers slot-decls -> slot-info
;;; inherits slots from supers and process slot-declaration forms.
;;;    supers     : list of super sort reference. (super-sort <rename-map>)
;;;                 * assumes that references to super class/reocord are
;;;                 already resolved, i.e, super-sort is a sort object.
;;;                  <rename-map> is nil or ast (%attr-rename "old-name"
;;;                  "new-name"). 
;;;    slot-decls : list of ast (%slot "slot-name" <sort-reference> <pre-term>) .
;;;                 <pre-term> is for specifying the default value, type is
;;;                 string or list of tokens, possibly be ni. 
;;;
;;; (1) inherits super attribures possibly with renaming attribute's names,
;;;     sorts or default values.
;;; (2) declare sort for each slot-name and its constructor.
;;; (3) define readers/writers for own slots.
;;; (4) default value is not parsed, returns it as is.
;;;
;;; Axioms for readers/writers are declared elsewhere.
;;;
;;; returns the list of slot declarations.
;;;  ==> slot declaration : ("slot-name" sort "default-value"
;;;                            (slot-consructor-method . pattern-variable))
;;; 
;;; Ex. a slot declaration '("slot1" <Sort-1>) of class Foo (no supers)
;;;  will be produces the following sort/operator declarations:
;;;  [ Slotslot1 < AttrId ]           -- sort for attribute(slot) identifier
;;;  op slot1 : -> Slotslot1          -- constructor
;;;  op slot1 : Foo -> Sort-1         -- reader
;;;  op set-slot1 : Foo Sort-1 -> Foo -- writer
;;; 

(defmacro slot-name-to-sort-name (??__name)
  `(concatenate 'string "Slot" (the simple-string ,??__name)))

(defun inherit-super-slots (super-ref module)
  (declare (type t super-ref)
           (type module module)
           (values list))
  (if (null (second super-ref))
      ;; no slot renaming
      (copy-list (crsort-slots (car super-ref))) ; might be modified later.

      ;; slot renaming.
      (let* ((super-sort (car super-ref))
             (super-slots (crsort-slots super-sort))
             (maps (mapcar #'(lambda (m)
                               (cons (%attr-rename-source m)
                                     (%attr-rename-target m)))
                           (second super-ref)))
             (inherited-slots nil))
        ;; a little error check
        (dolist (ren maps)
          (let ((slot (assoc (car ren) super-slots :test #'equal)))
            (unless slot
              (with-output-chaos-error ('invalid-rc-attributes)
                (format t "renaming super's attribute, no such attribute ~a in super sort ~a"
                        (car ren) (sort-id (car super-ref)))
                ))))
        ;; do renaming
        (dolist (sl super-slots)
          (let ((new-name (cdr (assoc (car sl) maps :test #'equal))))
            (if new-name
                ;; 
                (let ((new-slot (copy-list sl))
                      (new-slot-sort-name (slot-name-to-sort-name new-name))
                      (new-slot-sort nil))
                  (setf (car new-slot) new-name)
                  (push new-slot inherited-slots)
                  (setq new-slot-sort
                        (declare-sort-in-module (intern new-slot-sort-name)
                                                module))
                  (declare-subsort-in-module (list (list new-slot-sort
                                                         ':<
                                                         (method-coarity
                                                          (cr-slot-attribute-id-method sl))))
                                             module)
                  ;;
                  (multiple-value-bind (new-sl-op new-sl-method)
                      (declare-operator-in-module (list new-name)
                                                  nil
                                                  new-slot-sort
                                                  module)
                    (declare (ignore new-sl-op))
                    (setf (cr-slot-attribute-id new-slot)
                          (cons new-sl-method
                                (make-new-variable
                                 (concatenate 'string
                                              "VAR-" (string-upcase new-slot-sort-name))
                                 new-slot-sort)))))
                ;; no modification, inherit as is .
                (push (copy-list sl) inherited-slots))))
        (nreverse inherited-slots))))

;;; PROCESS-SLOT-DECLARATIONS module super-refs slot-decls
(defun process-slot-declarations (module cr-sort super-refs slot-decls)
  (declare (type module module)
           (type sort-struct cr-sort)
           (type t super-refs slot-decls)
           (values list))
  (with-in-module (module)
    (let ((super-slots nil)
          (own-slots nil))
      ;; INHERITS SUPER SLOTS.
      (dolist (super-ref super-refs)
        (let ((super-sort (car super-ref)))
          (if (crsort-p super-sort)
              (let ((inherited-slots (inherit-super-slots super-ref module)))
                (dolist (ihsl inherited-slots)
                  (when (assoc (car ihsl) super-slots :test #'equal)
                    (with-output-chaos-error ('invalid-rc-attribute)
                      (format t "duplicated attribute name ~a is inherited from supers."
                              (car ihsl))
                      ))
                  (push ihsl super-slots))))))
      ;; PROCESS OWN SLOTS.
      ;; WE DO NOT PARSE TERMS FOR DEFAULT VALUES HERE.
      ;; May include re-defining sorts or default value of super slots.
      (dolist (x slot-decls)
        (block next
          (let* ((sort (find-sort-in module (%slot-sort x)))
                 (slot-name (%slot-name x))
                 (slot-sort-name (slot-name-to-sort-name slot-name))
                 (slot-name-sort nil)
                 (slot-name-var nil)
                 the-slot)
            (unless sort
              (with-output-chaos-error ('no-such-sort)
                (format t "declaring record/class, no such sort ")
                (print-sort-ref (%slot-sort x))
                (print-next)
                (format t "for attribute ~a." (%slot-name x))
                ))
            ;;
            (when (assoc slot-name own-slots :test #'equal)
              (with-output-chaos-error ('invalid-rc-attribute)
                (format t "duplicated attributes ~a are declared" slot-name)
                ))
            ;; check sort changing or different default value.
            (let ((sup (assoc slot-name super-slots :test #'equal)))
              (when sup
                (if (sort<= sort (cr-slot-sort sup) *current-sort-order*)
                    ;; ok
                    (progn
                      ;; delete slot declaration from inherited ones
                      (setq super-slots (delete sup super-slots))
                      )
                    ;;
                    (with-output-chaos-error ('invalid-rc-attribute)
                      (format t "for attribute ~a, changed sort must be a susort of ~a, but declared as ~a"
                              (car x)
                              (sort-id (cr-slot-sort sup))
                              (sort-id sort))
                      ))))

            ;; declare slot's sort as an subsort of attribute-value
            (unless (sort<= sort *attr-value-sort* *current-sort-order*)
              (let ((supers (supersorts-no-err sort *current-sort-order*)))
                (if (null supers)
                    (declare-subsort-in-module `((,sort :< ,*attr-value-sort*))
                                               module)
                    (declare-subsort-in-module `((,@(maximal-sorts-no-error supers *current-sort-order*)
                                                  :< ,*attr-value-sort*))
                                               module))))
            
            ;; SORT FOR SLOT-NAME (Attribute Identifier)
            (setq slot-name-sort
                  (or (find-sort-in module slot-sort-name)
                      (declare-sort-in-module (intern slot-sort-name)
                                              module)))
            (unless (sort<= slot-name-sort *attribute-id-sort* *current-sort-order*)
              (declare-subsort-in-module (list (list slot-name-sort
                                                     ':<
                                                     *attribute-id-sort*))
                                         module))

            ;; 
            ;; (update-sort-order (module-sort-order module)) ***
            ;; Attribute Identifier CONSTRUCTOR
            (multiple-value-bind (sl-op sl-method)
                (declare-operator-in-module (list slot-name)
                                            nil
                                            slot-name-sort
                                            module
                                            :attribute-id)
              (declare (ignore sl-op))
              (setq slot-name-var
                    (make-new-variable
                     (concatenate 'string
                                  "VAR-" (string-upcase slot-sort-name))
                     slot-name-sort))
              (setq the-slot (list slot-name ; name
                                   sort ; sort
                                   (%slot-default x) ; default value
                                   (cons sl-method slot-name-var) ; attribute id
                                   nil  ; reader
                                   nil  ; writer
                                   ))
              (push the-slot own-slots)
              
              (let* ((slot-sort (cr-slot-sort the-slot))
                     (slot-name (cr-slot-name the-slot))
                     (reader (list slot-name))
                     (writer (list (concatenate 'string "set-" slot-name))))
                ;; READER
                (multiple-value-bind (r-op r-meth)
                    (declare-operator-in-module reader
                                                (list cr-sort)
                                                slot-sort
                                                module)
                  (declare (ignore r-op))
                  (setf (cr-slot-reader the-slot) r-meth))
                ;; WRITER
                (multiple-value-bind (op meth)
                    (declare-operator-in-module writer
                                                (list cr-sort slot-sort)
                                                cr-sort
                                                module)
                  (setf (cr-slot-writer the-slot) meth)
                  (declare-operator-strategy op '(1 2 0)))
                )))))
      ;;
      (nconc super-slots own-slots))))

;;; DECLARE-CR-INTERNAL mdoule name supers slot-descriptions type
;;;
;;; declare SIGNATURE for record/class sort.
;;; axioms will be declared elsewhere.
;;;
(defun make-make-name (name)
  (declare (type (or symbol simple-string) name)
           (values simple-string))
  (concatenate 'string "make" (string name)))

(defun make-id-sort-name (name type)
  (declare (type (or symbol simple-string) name)
           (type symbol type)
           (values symbol))
  (intern (format nil "~a~a"
                  (if (eq type 'class-sort) "Class" "Record")
                  name)))

(defun declare-cr-internal (module name supers slot-decls type &optional hidden)
  (declare (type module module)
           (type t name)
           (type list supers slot-decls)
           (type symbol type)
           (type (or null t) hidden)
           (values t))
  (multiple-value-bind (cr-sort super-sorts)
      (declare-cr-sort module name supers type hidden)
    (declare (type sort-struct cr-sort)
             (type list super-sorts))
    (unless (sort-struct-p cr-sort)
      (break "Panic non sort"))
    (let ((id-sort-name (make-id-sort-name name type))
          id-sort
          (constructor-name (if (eq type 'class-sort)
                                ;; NOTE: the order is significant
                                (list '("<" "_" ":" "_" "|" "_" ">")
                                      '("<" "_" ":" "_" ">"))
                                (list '("_" "{" "_" "}")
                                      '("_" "{" "}"))))
          const-arities)
      ;; RECORD&CLASS IDENTIFIER --------------------------------
      (setq id-sort (declare-sort-in-module id-sort-name module 'sort hidden))
      (setq const-arities
            (if (eq type 'class-sort)
                (list (list *object-identifier-sort*
                            id-sort
                            *attribute-list-sort*)
                      (list *object-identifier-sort*
                            id-sort)
                      (list *object-identifier-sort*
                            id-sort))
                (list (list id-sort *attribute-list-sort*)
                      (list id-sort))))
      (if supers
          (let ((supers-id (mapcar #'(lambda (x) (sort-to-id-sort (car x) module))
                                   super-sorts)))
            (declare-subsort-in-module (list (list* id-sort ':< supers-id))
                                       module
                                       hidden))
          (declare-subsort-in-module (list (list id-sort ':<
                                                 (if (eq type 'class-sort)
                                                     *class-id-sort*
                                                     *record-id-sort*)))
                                     module))
      ;; MESSAGE SORT FOR CLASS SORTS ------------------------------
      (when (eq type 'class-sort)
        (let* ((msg-sort-name (format nil "~aMessage" name))
               (msg-sort (declare-sort-in-module (intern msg-sort-name) module)))
          (declare-subsort-in-module (list (list msg-sort ':< *message-sort*))
                                     module)))
      ;;
      ;; (update-sort-order (module-sort-order module))
      ;;
      ;; RECORD/CLASS ID -------------------------------------------
      (multiple-value-bind (op meth)
          (declare-operator-in-module (list name) () id-sort module :crid)
        (declare (ignore op))
        (unless meth
          (error "PANIC! no method returned"))
        (setf (crsort-idconstr cr-sort) (cons meth
                                        (make-new-variable "RCID" id-sort)))
        
        ;; CONSTRUCTOR ---------------------------------------------
        (dotimes (x 2)
          (multiple-value-bind (op meth)
              (declare-operator-in-module (nth x constructor-name)
                                          (nth x const-arities)
                                          cr-sort
                                          module
                                          (if (= 0 x)
                                              (if (eq type 'class-sort)
                                                  :object
                                                  :record)
                                              :object-ref)
                                          )
            (declare (ignore op))
            (if (= x 0)
                (setf (crsort-constr-method cr-sort) meth))))

        ;; operator makeFoo ----------------------------------------
        (if (eq type 'class-sort)
            ;; MAKE FOR CLASS ---
            (let ((op-name (make-make-name name)))
              ;; (declare (ignore make-op))
              ;; (1) makeFoo : ObjectId Attributes -> Foo
              (multiple-value-bind (make-op make-meth)
                  (declare-operator-in-module (list op-name)
                                              (list *object-identifier-sort*
                                                    *attribute-list-sort*)
                                              cr-sort
                                              module)
                (declare (ignore make-op))
                (setf (crsort-make-1 cr-sort) make-meth))
              
              ;; (2) makeFoo : ObjectId -> Foo
              (multiple-value-bind (make-op make-meth)
                  (declare-operator-in-module (list op-name)
                                              (list *object-identifier-sort*)
                                              cr-sort
                                              module)
                (declare (ignore make-op))
                (setf (crsort-make-2 cr-sort) make-meth))
              
              ;; (3) makeFoo_ : Attributes -> Foo
              (multiple-value-bind (make-op make-meth)
                  (declare-operator-in-module (list op-name "_")
                                              (list *attribute-list-sort*)
                                              cr-sort
                                              module)
                (setf (crsort-make-3 cr-sort) make-meth)
                (declare-operator-precedence make-op 0))
              
              ;; (4) makeFoo : -> Foo
              (multiple-value-bind (make-op make-meth)
                  (declare-operator-in-module (list op-name)
                                              nil
                                              cr-sort
                                              module)
                (declare (ignore make-op))
                (setf (crsort-make-4 cr-sort) make-meth))
              )

            ;; MAKE FOR RECORD ---
            (let ((op-name (list (make-make-name name))))
              ;; makeFoo : Attrs -> Foo
              (multiple-value-bind (make-op make-meth)
                  (declare-operator-in-module op-name
                                            (list *attribute-list-sort*)
                                            cr-sort
                                            module)
                (declare (ignore make-op))
                (setf (crsort-make-1 cr-sort) make-meth))
              
              ;; makeFoo : -> Foo
              (multiple-value-bind (make-op make-meth)
                  (declare-operator-in-module op-name
                                              nil
                                              cr-sort
                                              module)
                (declare (ignore make-op))
                (setf (crsort-make-2 cr-sort) make-meth))
              
              )
            )
        
      
        ;; ATTRIBUTE IDS,READERS,WRITERS ----------------------------
        (setf (crsort-slots cr-sort)
              (process-slot-declarations module cr-sort super-sorts slot-decls))
        ))
    ;;
    cr-sort))

;;; Declaring CLASS
;;;
(defun declare-class-in-module (module name supers slot-decls &optional hidden)
  (let ((class-sort (declare-cr-internal module
                                         name
                                         supers
                                         slot-decls
                                         'class-sort
                                         hidden)))
    class-sort))

;;; Declaring RECORD
;;;
(defun declare-record-in-module (module name supers slot-decls &optional hidden)
  (let ((record-sort (declare-cr-internal module
                                          name
                                          supers
                                          slot-decls
                                          'record-sort
                                          hidden)))
    record-sort))
  
;;; DECLARING AXIOMS for ACCESSORS & MAKE.
;;;
(defun declare-class-axioms (module sort)
  (unless (crsort-is-a-copy sort)
    (with-in-module (module)
      (let* ((id-var (make-new-variable "OBJID" *object-identifier-sort*))
             (cid-var (crsort-id-variable sort))
             (attrs-var (make-new-variable "ATTRS" *attribute-list-sort*)))
        (macrolet ((make-object-pattern (slot var)
                     ` (make-applform sort
                                      (crsort-constr-method sort)
                                      (list id-var
                                            cid-var
                                            (make-applform
                                             *attribute-list-sort*
                                             *attribute-list-constructor*
                                             (list (make-applform
                                                    *attribute-sort*
                                                    *attribute-constructor*
                                                    (list
                                                     (cr-slot-attribute-id-variable ,slot)
                                                     ,var))
                                                   attrs-var)))))
                   )
          ;; AXIOMS for READERS & WRITERS of EACH ATTRIBUTE
          (dolist (slot (crsort-slots sort))
            (let* ((var (make-new-variable "VAL" (cr-slot-sort slot)))
                   (object-pattern (make-object-pattern slot var)))
            
              ;; READER -------------------------------------------------------
              (let (lhs
                    rhs
                    ax)
                (setf lhs (make-applform (cr-slot-sort slot)
                                         (cr-slot-reader slot)
                                         (list object-pattern)))
                (setf rhs var)
                (setf ax (make-simple-axiom lhs rhs :equation))
                (add-axiom-to-module *current-module* ax)
                )
              ;; WRITER -------------------------------------------------------
              (let ((new-var (make-new-variable "NEW-VAL" (cr-slot-sort slot)))
                    lhs
                    rhs
                    ax)
                (setf lhs (make-applform sort
                                         (cr-slot-writer slot)
                                         (list (make-object-pattern slot var)
                                               new-var)))
                (setf rhs (make-object-pattern slot new-var))
                (setf ax (make-simple-axiom lhs rhs :rule))
                (add-axiom-to-module *current-module* ax))))

          ;; AXIOMS for makeFoo ----------------------------------------------
          (let* ((*print-case* :upcase)
                 (*print-escape* nil)
                 (rhs-form-1 (format nil "#!! (make-class-instance ~a '~s ~a)"
                                     (variable-name id-var)
                                     (sort-id sort)
                                     (variable-name attrs-var)
                                     ))
                 (rhs-form-2 (format nil "#!! (make-class-instance ~a '~s)"
                                     (variable-name id-var)
                                     (sort-id sort)))
                 (rhs-form-3 (format nil "#!! (make-class-instance-allocating-id '~s ~a)"
                                     (sort-id sort)
                                     (variable-name attrs-var)))
                 (rhs-form-4 (format nil "#!! (make-class-instance-allocating-id '~s)"
                                     (sort-id sort)))
                 lhs
                 rhs
                 ax)
            ;; (1) makeFoo : ObjectId Attributes -> Foo
            (setf lhs (make-applform sort
                                     (crsort-make-1 sort)
                                     (list id-var attrs-var)))
            (setf rhs (simple-parse-from-string* rhs-form-1))
            (setf ax (make-simple-axiom lhs rhs :rule))
            (add-axiom-to-module *current-module* ax)
            ;; (2) makeFOO : ObjectID -> Foo
            (setf lhs (make-applform sort
                                     (crsort-make-2 sort)
                                     (list id-var)))
            (setf rhs (simple-parse-from-string* rhs-form-2))
            (setf ax (make-simple-axiom lhs rhs :rule))
            (add-axiom-to-module *current-module* ax)
            ;; (3) makeFoo_ : Attributes -> Foo
            (setf lhs (make-applform sort
                                     (crsort-make-3 sort)
                                     (list attrs-var)))
            (setf rhs (simple-parse-from-string* rhs-form-3))
            (setf ax (make-simple-axiom lhs rhs :rule))
            (add-axiom-to-module *current-module* ax)
            ;; (4) makeFoo : -> Foo
            (setf lhs (make-applform sort (crsort-make-4 sort) nil))
            (setf rhs (simple-parse-from-string* rhs-form-4))
            (setf ax (make-simple-axiom lhs rhs :rule))
            (add-axiom-to-module *current-module* ax)
            ))))))

(defun declare-record-axioms (module sort)
  (unless (crsort-is-a-copy sort)
    (with-in-module (module)
      (let ((*parse-variables* nil)
            (*print-case* :upcase)
            (*print-escape* nil))
        (let ((rid-var (make-new-variable "RID" (sort-to-id-sort sort *current-module*)))
              (attrs-var (make-new-variable "ATTRS" *attribute-list-sort*)))
          (macrolet ((make-record-pattern (slot var)
                       ` (make-applform sort
                                        (crsort-constr-method sort)
                                        (list rid-var
                                              (make-applform
                                               *attribute-list-sort*
                                               *attribute-list-constructor*
                                               (list
                                                (make-applform
                                                 *attribute-sort*
                                                 *attribute-constructor*
                                                 (list
                                                  (cr-slot-attribute-id-variable ,slot)
                                                  ,var))
                                                attrs-var))))))
            ;; AXOMS for READERS & WRITERS of EACH ATTRIBUTE
            (dolist (slot (crsort-slots sort))
              (let* ((var (make-new-variable "VAL" (cr-slot-sort slot)))
                     (record-pattern (make-record-pattern slot var)))
                ;; READER -----------------------------------------------------
                (let (lhs
                      rhs
                      ax)
                  (setf lhs (make-applform (cr-slot-sort slot)
                                           (cr-slot-reader slot)
                                           (list record-pattern)))
                  (setf rhs var)
                  (setf ax (make-rule :lhs lhs :rhs rhs
                                      :condition *bool-true*
                                      :id-condition nil
                                      :type :equation
                                      :kind nil
                                      :labels nil))
                  (add-axiom-to-module *current-module* ax)
                  )

                ;; WRITER ---------------------------------------------------
                (let ((new-var (make-new-variable "NEW-VAL" *cosmos*))
                      lhs
                      rhs
                      ax)
                  (setf lhs
                        (make-applform sort
                                       (cr-slot-writer slot)
                                       (list (make-record-pattern slot var)
                                             new-var)))
                  (setf rhs (make-record-pattern slot new-var))
                  (setf ax (make-rule :lhs lhs :rhs rhs
                                      :condition *bool-true*
                                      :id-condition nil
                                      :type :equation
                                      :kind nil
                                      :labels nil))
                  (add-axiom-to-module *current-module* ax))))

            ;; MAKE ---------------------------------------------------------
            (let ((rhs-form-1 (format nil "#!! (make-record-instance '~s ~a)"
                                      (sort-id sort)
                                      (variable-name attrs-var)
                                      ))
                  (rhs-form-2 (format nil "#!! (make-record-instance '~s)"
                                      (sort-id sort)))
                  lhs
                  rhs
                  ax)
              ;; (1) makeFoo : Attributes -> Foo
              (setf lhs (make-applform sort
                                       (crsort-make-1 sort)
                                       (list attrs-var)))
              (setf rhs (simple-parse-from-string* rhs-form-1))
              (setf ax (make-simple-axiom lhs rhs :equation))
              (add-axiom-to-module *current-module* ax)
              ;; (2) makeFoo : -> Foo
              (setf lhs (make-applform sort
                                       (crsort-make-2 sort)
                                       nil))
              (setf rhs (simple-parse-from-string* rhs-form-2))
              (setf ax (make-simple-axiom lhs rhs :equation))
              (add-axiom-to-module *current-module* ax)
              )))))))

;;;-----------------------------------------------------------------------------
;;; MAKE.FOO
;;;-----------------------------------------------------------------------------

(defun make-class-instance (id class-id &optional attrs)
  (when (find-instance id)
    (with-output-chaos-error ('invalid-object-id)
      (princ "An object with identifier ")
      (print-chaos-object id)
      (print-next)
      (princ " is already exists.")
      ))
  (let* ((class-sort (or (find-sort-in *current-module* class-id)
                         (error "Internal error no class ~a" class-id)))
         (attr-list (complete-attributes class-sort attrs))
         (cid-method (crsort-id-method class-sort))
         (const-method (crsort-constr-method class-sort))
         (instance nil))
    (setf instance 
          (make-applform class-sort
                         const-method
                         (list id
                               (make-applform (method-coarity cid-method) cid-method nil)
                               attr-list)))
    (register-instance instance)
    instance))


;;; ALLOCATES UNIQUE IDENTIFIER

(defvar *id-allocation-table* (make-hash-table :test #'eq :size 50))
(defvar *gensym-prefix* (intern "ID#-"))
(defun generate-unique-identifier (&optional prefix)
  (cond (prefix (let ((so-far (gethash prefix *id-allocation-table*))
                      new-id)
                  (unless so-far
                    (setf so-far
                          (setf (gethash prefix *id-allocation-table*) 0)))
                  (setf new-id (intern (format nil "~a-~d" prefix so-far)))
                  (setf (gethash prefix *id-allocation-table*)
                        (1+ (the fixnum so-far)))
                  new-id))
        (t (generate-unique-identifier *gensym-prefix*))))

#|| NOT USED
(defun make-unique-object-identifier (class)
  (generate-unique-identifier (class-identifier-prefix class)))
||#

(defun make-class-instance-allocating-id (class-id &optional attrs)
  (let ((id (make-bconst-term *identifier-sort*
                              (generate-unique-identifier class-id))))
    (make-class-instance id class-id attrs)))

(defun make-record-instance (record-id &optional attrs)
  (let* ((record-sort (or (find-sort-in *current-module* record-id)
                          (error "Internal error no record ~a" record-id)))
         (attr-list (complete-attributes record-sort attrs))
         (rid-method (crsort-id-method record-sort))
         (const-method (crsort-constr-method record-sort))
         (instance nil))
    ;; (break)
    (setf instance 
          (make-applform record-sort
                         const-method
                         (list (make-applform (method-coarity rid-method) rid-method nil)
                               attr-list)))
    instance))

;;; ** TODO ** TYPE CHECK ~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~
;;;
(defun complete-attributes (sort attrs)
  ;; (format t "~&complete-attributes sort = ")
  ;; (print-chaos-object sort)
  ;; (format t "~& attrs = ")
  ;; (print-chaos-object attrs)
  (let* ((attr-list (cond ((and attrs
                                (sort= (term-sort attrs) *attribute-list-sort*))
                           (list-ac-subterms attrs (term-method attrs)))
                          (attrs (list attrs))
                          (t nil)))
         (specified-slot-names (mapcar #'(lambda (x)
                                           (car (method-symbol (term-head
                                                                (term-arg-1 x)))))
                                       attr-list))
         (slot-info (crsort-slots sort))
         (all-slot-names (mapcar #'car slot-info))
         (slots-to-be-filled (set-difference all-slot-names specified-slot-names
                                             :test #'equal)))
    ;; (format t "~& slots-to-be-filled = ~a" slots-to-be-filled)
    (let ((slots nil))
      (dolist (s slots-to-be-filled)
        (let* ((sinfo (assoc s slot-info :test #'equal))
               (dvalue (third sinfo))
               (dterm nil))
          (unless sinfo (error "Internal error, no slot ~a" s))
          (cond (dvalue (setq dterm
                              (let ((*parse-variables* nil))
                                (simple-parse-from-string* (format nil "~a = ~a" s dvalue)
                                                           *current-module*
                                                           *attribute-sort*)))
                        (unless dterm
                          (with-output-chaos-error ('invalid-rc-attribute-value)
                            (format t
                                    "invalid initial value ~a for slot ~a of record/class ~a."
                                    dvalue s (sort-id sort))
                            ))
                        (push dterm slots))
                (t (setq dterm
                         (let ((*parse-variables* nil))
                           (simple-parse-from-string* (format nil "~a = void-bottom" s)
                                                      *current-module*
                                                      *attribute-sort*)))
                   (push dterm slots)))))
      (if slots
          (let ((new-attrs (append attr-list slots)))
            (declare (type list new-attrs))
            (if (<= 2 (the fixnum (length new-attrs)))
                (make-right-assoc-normal-form *attribute-list-constructor*
                                              new-attrs)
                (car new-attrs)))
          attrs))))

      
;;; EOF
