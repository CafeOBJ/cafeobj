;;;-*-Mode:LISP; Package: CHAOS; Base:10; Syntax:Common-lisp -*-
;;; $Id: builtins.lisp,v 1.13 2007-01-26 10:38:35 sawada Exp $
(in-package :chaos)
#|=============================================================================
                                System:CHAOS
                                Module:boot
                              File:builtins.lisp
=============================================================================|#

;;; INTIALIZE DB 

(eval-when (:execute :load-toplevel)
  (clear-global-db)
  (clear-trs-db)
  (unless *term-memo-table*
    (create-term-memo-table))
  )

;;;*****************************************************************************
;;; HARD-WIRED STUFF ***********************************************************
;;;*****************************************************************************

(defparameter cosmos-sort-ref `(%sort-ref ,(string $name-cosmos) nil))
(defparameter universal-sort-ref `(%sort-ref ,(string $name-universal) nil))
(defparameter huniversal-sort-ref `(%sort-ref ,(string $name-huniversal) nil))

(defun boot-universal-module ()
  (setq *universal-module* (define-builtin-module "CHAOS:UNIVERSAL"))
  (setq *term-sort* (define-builtin-sort $name-term *universal-module*))
  (setq *cosmos* (define-builtin-sort $name-cosmos *universal-module*))
  (setq *universal-sort* (define-builtin-sort $name-universal *universal-module*))
  (setq *huniversal-sort* (define-builtin-sort $name-huniversal *universal-module*))
  (setq *bottom-sort* (define-builtin-sort $name-bottom *universal-module*))
  (setq *hbottom-sort* (define-builtin-sort $name-hbottom *universal-module*))
  (setf (sort-is-hidden *huniversal-sort*) t)
  (setf (sort-is-hidden *hbottom-sort*) t)
  (setq sup-universal-sort-name
	(intern
	 (concatenate 'string (string (sort-id *universal-sort*))
                  "."
                  (make-module-print-name2 (sort-module *universal-sort*)))))
  (setq sup-huniversal-sort-name
	(intern
	 (concatenate 'string (string (sort-id *huniversal-sort*))
                  "."
                  (make-module-print-name2 (sort-module *huniversal-sort*)))))
  (compile-module *universal-module*))

(defun boot-parser-module ()
  (setq *parser-module* (define-builtin-module "CHAOS:PARSER"))
  (with-in-module (*parser-module*)
    ;; import Universal
    (import-module *parser-module* :protecting *universal-module*)
    ;; Sorts for syntax errors
    (let ((syntax-err (define-builtin-sort '|SyntaxErr| *parser-module*))
          (type-err (define-builtin-sort '|TypeErr| *parser-module*))
	  (sort-id (define-builtin-sort '|SortId| *parser-module*)))
      (setf *syntax-err-sort* syntax-err)
      (setf *type-err-sort* type-err)
      (setf *sort-id-sort* sort-id)
      (declare-subsort-in-module `((,*type-err-sort* :< ,*syntax-err-sort*))
                                 *parser-module*))
    ;; operators for syntax errors
    (let ((partial-op (declare-operator-in-module '("parsed:[" "_" "],"
                                                    "rest:[" "_" "]")
                                                  (list *universal-sort*
                                                        *universal-sort*)
                                                  *syntax-err-sort*
                                                  *parser-module*)))
      (setf *partial-op* partial-op)))
  ;;
  (let* ((opinfos (module-all-operators *parser-module*))
         (partial-meth (car (operator-methods *partial-op* opinfos))))
    (if partial-meth
        (setf *partial-method* partial-meth)
      (break "!! Panic! : cannot find partial method"))
    (compile-module *parser-module*)))

(defun boot-chaos ()
  (setq *chaos-module* (define-builtin-module "CHAOS"))
  (boot-universal-module)
  (boot-parser-module)
  (import-module *chaos-module* :protecting *universal-module*)
  (import-module *chaos-module* :protecting *parser-module*)
  (compile-module *chaos-module*)
  (setq *chaos-sort-order* (module-sort-order *chaos-module*))
  ;; put here for a reason.
  (setq *match-dep-var* (make-variable-term *cosmos* 'REST))
  (setq *kernel-hard-wired-builtin-modules* (list *universal-module*
                                                  *parser-module*
                                                  *chaos-module*))
  t
  )

(defun boot-meta-module ()
  (setq *chaos-meta* (define-builtin-module "CHAOS:META"))
  ;; builtin sorts of internal objects-------------------------------
  ;; *Module* 
  (setq *module-sort* (define-builtin-sort $name-module *chaos-meta*))
  ;; *Import*
  (setq *import-sort* (define-builtin-sort $name-import *chaos-meta*))
  ;; *Signature*
  (setq *signature-sort* (define-builtin-sort $name-signature *chaos-meta*))
  ;; *AxiomSet*
  (setq *axiomset-sort* (define-builtin-sort $name-axiomset *chaos-meta*))
  ;; *Trs*
  (setq *trs-sort* (define-builtin-sort $name-trs *chaos-meta*))
  ;; *Sort*
  (setq *sort-sort* (define-builtin-sort $name-sort *chaos-meta*))
  ;; *Operator*
  (setq *operator-sort* (define-builtin-sort $name-operator *chaos-meta*))
  ;; *OpTheory*
  (setq *optheory-sort* (define-builtin-sort $name-optheory *chaos-meta*))
  ;; *Axiom*
  (setq *axiom-sort* (define-builtin-sort $name-axiom *chaos-meta*))
  ;; *CafeList*
  (setq *chaos-list-sort* (define-builtin-sort $name-chaos-list *chaos-meta*))
  ;; *ChaosObject*
  (setq *chaos-object* (define-builtin-sort $name-chaos-object *chaos-meta*))
  ;; *Void*
  (setq *chaos-void-sort* (define-builtin-sort $name-void *chaos-meta*))
  ;; *ChaosExpr*
  (setq *chaos-expr-sort* (define-builtin-sort $name-chaos-expr *chaos-meta*))
  ;; *Substitution*
  (setq *subst-sort* (define-builtin-sort $name-subst *chaos-meta*))
  ;; *Parameter*
  (setq *parameter-sort* (define-builtin-sort $name-parameter *chaos-meta*))
  )

(defun print-ast-dict ()
  (maphash #'(lambda (x y)
               (format t "~&key=~a, entries -------------------" x)
               (dolist (elt y)
                 (let ((ee (cdr elt)))
                   (terpri)
                   (dolist (e ee)
                     (case (car e)
                       (token (princ (cdr e)))
                       (argument (print-chaos-object (cddr e))))))))
           *builtin-ast-dict*))

;;;*****************************
;;; HARD-WIRED BUILTIN MODULES *
;;;*****************************************************************************
;;; The followings are hard-wired modules which are not allowed to
;;; be altered by users.
;;;*****************************************************************************

;;; CHAOS HARDWIRED MODULES ----------------------------------------------------
;;; TRIV
;;; TRUTH-VALUE
;;; NZNAT-VALUE
;;; NAT-VALUE
;;; INT-VALUE
;;; RAT-VALUE
;;; FLOAT-VALUE
;;; CHAR-VALUE
;;; STRING-VALUE
;;; CHAOS:META
;;;
(defun install-chaos-hard-wired-modules ()
  (setq *dribble-ast* nil)
  (setq *ast-log* nil)
  (setq *last-module* nil *current-module* nil)
  (setq *include-bool* nil)
  (setq *include-rwl* nil)
  (setq *regularize-signature* nil)
  (boot-chaos)
  (boot-meta-module)
  (eval-ast-if-need '(%module-decl "TRIV" :theory :hard
                      ((%psort-decl (%sort-ref "Elt" nil))
                       (%sort-decl (%sort-ref "Elt" nil) nil))))
  (eval-ast-if-need '(%module-decl "TRUTH-VALUE" :object :hard
                      ((%psort-decl (%sort-ref "Bool" nil))
                       (%sort-decl (%sort-ref "Bool" nil) nil)
                       (%op-decl ("false") nil (%sort-ref "Bool" nil)
                        (%opattrs nil nil nil nil nil t nil)
                        nil)
                       (%op-decl ("true") nil (%sort-ref "Bool" nil)
                        (%opattrs nil nil nil nil nil t nil)
                        nil))))
  (setup-truth-value)
  ;;
  (eval-ast-if-need '(%module-decl "NZNAT-VALUE" :object :hard
                      ((%psort-decl (%sort-ref "NzNat" nil))
                       (%bsort-decl "NzNat" is-nznat-token
                        create-nznat prin1 is-nznat nil))))
  (eval-ast-if-need '(%module-decl "NAT-VALUE" :object :hard
                      ((%import :protecting "NZNAT-VALUE" nil)
                       (%psort-decl (%sort-ref "Nat" nil))
                       (%bsort-decl "Nat" is-nat-token create-nat
                        prin1 is-nat nil)
                       (%bsort-decl "Zero" is-zero-token create-zero
                        prin1 is-zero nil)
                       (%subsort-decl
                        (nil (%sort-ref "NzNat" nil) :<
                         (%sort-ref "Nat" nil)))
                       (%subsort-decl
                        (nil (%sort-ref "Zero" nil) :<
                         (%sort-ref "Nat" nil))))))
  (eval-ast-if-need '(%module-decl "INT-VALUE" :object :hard
                      ((%import :protecting "NAT-VALUE" nil)
                       (%psort-decl (%sort-ref "Int" nil))
                       (%bsort-decl "Int" is-int-token create-int
                        prin1 is-int nil)
                       (%bsort-decl "NzInt" is-nzint-token
                        create-nzint prin1 is-nzint nil)
                       (%subsort-decl
                        (nil (%sort-ref "Nat" nil) :<
                         (%sort-ref "Int" nil)))
                       (%subsort-decl
                        (nil (%sort-ref "NzNat" nil) :<
                         (%sort-ref "NzInt" nil) :<
                         (%sort-ref "Int" nil))))))
  (eval-ast-if-need '(%module-decl "RAT-VALUE" :object :hard
                      ((%import :protecting "INT-VALUE" nil)
                       (%psort-decl (%sort-ref "Rat" nil))
                       (%bsort-decl "Rat" is-rat-token create-rat
                        rat-print rationalp nil)
                       (%bsort-decl "NzRat" is-nzrat-token
                        create-nzrat rat-print is-nzrat nil)
                       (%subsort-decl
                        (nil (%sort-ref "Int" nil) :<
                         (%sort-ref "Rat" nil)))
                       (%subsort-decl
                        (nil (%sort-ref "NzInt" nil) :<
                         (%sort-ref "NzRat" nil) :<
                         (%sort-ref "Rat" nil))))))
  (eval-ast-if-need '(%module-decl "FLOAT-VALUE" :object :hard
                      ((%psort-decl (%sort-ref "Float" nil))
                       (%bsort-decl "Float" is-float-token
                        create-float print-float is-float nil))))
  
  (eval-ast-if-need '(%module-decl "ID" :object :hard
                      ((%psort-decl (%sort-ref "Id" nil))
                       (%bsort-decl "Id" is-id-token create-id
                        print-id is-id nil))))
  (setup-id)
  (eval-ast-if-need '(%module-decl "QID" :object :hard
                      ((%psort-decl (%sort-ref "Id" nil))
                       (%bsort-decl "Id" is-qid-token create-qid
                        print-qid is-qid nil))))
  (setup-qid)
  (eval-ast-if-need '(%module-decl "CHAR-VALUE" :object :hard
                      ((%psort-decl (%sort-ref "Character" nil))
                       (%bsort-decl "Character" is-character-token
                        create-character print-character
                        is-character nil))))
  (install-character)
  (eval-ast-if-need '(%module-decl "STRING-VALUE" :object :hard
                      ((%psort-decl (%sort-ref "String" nil))
                       (%bsort-decl "String" nil nil prin1 stringp nil))))
  (install-string)
  ;;
  ;;
  (setq *last-module* nil *current-module* nil)
  (setq *include-bool* t)
  (setq *include-rwl* t)
  )

;;;******************************
;;; SOFT-WIRED BUILT-IN MODULES *
;;;*****************************************************************************
;;; The followings are also builtins, but user may change their definitions.
;;;*****************************************************************************


;;; CHAOS System SOFT-WIRED BUILTIN MODULES
;;; ** We want the definitions to be saved for recovering them afterwards.
;;;

(defun install-chaos-soft-wired-modules ()
  (let ((*dribble-ast* nil))
    (setq *ast-log* nil)
    (setq *include-bool* t)
    (setq *include-rwl* t)
    (setq *last-module* nil
          *current-module* nil)
    (setq *regularize-signature* nil)
    ;; set recover proc.
    (setq *system-soft-wired*
	  '((%lisp-eval (install-chaos-soft-wired-modules))))
    ))

(defun chaos-misc-init ()
  (setq *print-ignore-mods* *kernel-hard-wired-builtin-modules*)
  (unless *apply-ignore-modules*
    (setq *apply-ignore-modules* *print-ignore-mods*))
  )

;;; BUILTIN UNIVERSALLY DEFINED OPERATORS
;;;
(defun init-builtin-universal ()
  (setq *bi-universal-operators* nil)
  (and *identical* (push *identical* *bi-universal-operators*))
  (and *nonidentical* (push *nonidentical* *bi-universal-operators*))
  (and *bool-if* (push *bool-if* *bi-universal-operators*))
  (and *bool-equal* (push *bool-equal* *bi-universal-operators*))
  (and *bool-nonequal* (push *bool-nonequal* *bi-universal-operators*))
  (and *beh-eq-pred* (push *beh-eq-pred* *bi-universal-operators*))
  (and *rwl-predicate* (push *rwl-predicate* *bi-universal-operators*))
  (and *rwl-predicate2* (push *rwl-predicate2* *bi-universal-operators*))
  )

;;;
;;; TRAM INITIALIZATION
;;; TRAM built-in sorts & operations.
;;;
(defvar *z-nznat-value* nil)
(defvar *z-nat-value* nil)
(defvar *z-int-value* nil)
(defvar *z-rat-value* nil)
(defvar *z-nznat* nil)
(defvar *z-nat* nil)
(defvar *z-int* nil)
(defvar *z-rat* nil)
(defvar *z-float-value* nil)
(defvar *z-float* nil)
(defvar *z-qid* nil)
(defvar *z-char-value* nil)
(defvar *z-char* nil)
(defvar *z-string-value* nil)
(defvar *z-string* nil)

(defun get-z-module-or-panic (name)
  (or (find-module-in-env (normalize-modexp name))
      (with-output-panic-message ()
        (format t "internal error, could not find ~a" name)
        (break))))

(defun setup-tram-bool-modules ()
  (setq *tram-bool-modules* nil)
  (and *truth-module*
       (push *truth-module* *tram-bool-modules*))
  (and *bool-module*
       (push *bool-module* *tram-bool-modules*))
  (and *rwl-module*
       (push *rwl-module* *tram-bool-modules*)))

(defun init-tram-bi-modules ()
  (setq *z-nznat-value* (get-z-module-or-panic "NZNAT-VALUE"))
  (setq *z-nat-value* (get-z-module-or-panic "NAT-VALUE"))
  (setq *z-int-value* (get-z-module-or-panic "INT-VALUE"))
  (setq *z-rat-value* (get-z-module-or-panic "RAT-VALUE"))
  (setq *z-float-value* (get-z-module-or-panic "FLOAT-VALUE"))
                                        ; (setq *z-nznat* (get-z-module-or-panic "NZNAT"))
                                        ; (setq *z-nat* (get-z-module-or-panic "NAT"))
                                        ; (setq *z-int* (get-z-module-or-panic "INT"))
                                        ; (setq *z-rat* (get-z-module-or-panic "RAT"))
                                        ; (setq *z-float* (get-z-module-or-panic "FLOAT"))
  (setq *z-qid* (get-z-module-or-panic "QID"))
  (setq *z-char-value* (get-z-module-or-panic "CHAR-VALUE"))
                                        ; (setq *z-char* (get-z-module-or-panic "CHARACTER"))
  (setq *z-string-value* (get-z-module-or-panic "STRING-VALUE"))
                                        ; (setq *z-string* (get-z-module-or-panic "STRING"))
  (setq *tram-builtin-modules*
	(list *z-nznat-value*
	      *z-nat-value*
	      *z-int-value*
                                        ; *z-nznat* *z-nat* *z-int*
	      *z-rat-value*
                                        ; *z-rat*
	      *z-float-value*
                                        ; *z-float*
	      *z-qid*
	      *z-char-value*
                                        ; *z-char*
	      *z-string-value*
                                        ; *z-string*
	      ))
  (setup-tram-bool-modules))

;;;
;;; BOOT BUILTIN MODULES
;;;
(eval-when (:execute :load-toplevel)
  (install-chaos-hard-wired-modules)
  (install-chaos-soft-wired-modules)
  (init-tram-bi-modules)
  (init-builtin-universal)
  (chaos-misc-init))

;;;
;;; EOF
