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
                                 File:trs.lisp
=============================================================================|#
#-:chaos-debug
(declaim (optimize (speed 3) (safety 0) #-GCL (debug 1)))
#+:chaos-debug
(declaim (optimize (speed 1) (safety 3) #-GCL (debug 3)))

;;; (defvar *on-trs-debug* nil)

;;; DESCRIPTION ===============================================================
;;; Generic TRS interface.
;;; Symbolic representation of TRS corresponding to Chaos module.
;;; All of the constructs of TRS are represented by some list of lisp symbols
;;; excepting module names.
;;; ---------------------------------------------------------------------------

;; (declaim (special *current-trs*))    ; not used now
;; (defvar *current-trs* nil)

(defun trs-get-mod-or-error (modexp)
  (if (module-p modexp)
      modexp
      (let ((modval nil))
        (cond ((null modexp)
               (setq modval (eval-mod nil)))
              ((stringp modexp)
               (setq modval (eval-mod (list modexp))))
              (t (with-output-chaos-error ('invalid-modexp)
                   (format t "illegal modexp ~a" modexp)
                   )))
        (if modval
            modval
            (with-output-chaos-error ('unknown-mod)
              (format t "could not evaluate modexp ~a" modexp)
              )))))

(defun get-module-trs-or-error (modexp)
  (get-module-trs (trs-get-mod-or-error modexp)))

;;;
;;; GET-MODULE-TRS
;;;
(defun get-module-trs (&optional modexp &aux module)
  (setq module (trs-get-mod-or-error modexp))
  (let ((trs (module-trs module)))
    (if (need-rewriting-preparation module)
        (progn
          (compile-module module)
          (chaos->trs module))
        (if (null (trs$sort-name-map trs))
          (chaos->trs module)))
    trs))

;;;
;;; CAFEOBJ->TRS
;;;
(defun chaos->trs (mod)
  (let ((trs (module-trs mod)))
    (initialize-trs-ext-interface trs)
    ;;
    (make-sort-name-map trs)
    (make-trs-sort-graph trs)
    (make-trs-op-maps trs)
    (fix-trs-ids trs)
    ;; (make-trs-axioms trs)
    (make-trs-builtin-op-maps trs)
    trs))

(defun print-chaos-trs (trs &optional (stream *standard-output*)
                            &rest ignore)
  (declare (ignore ignore))
  (let ((*print-circle* nil)
        (*print-case* :downcase)
        (*print-escape* nil))
    (prin1
     (make-trs-print-form trs)
     stream)
    (values)))

(defun make-trs-print-form (trs &optional (mod (trs$module trs)))
  (with-in-module (mod)
    ` (:trs
       ,(make-trs-module-name mod)
       :sorts
       ,(mapcar #'cdr (trs$sort-name-map trs))
       :subsorts
       ,(trs$sort-graph trs)
       :error-sorts
       ,(trs$err-sorts trs)
       :operators
       ,(mapcar #'cdr (trs$op-info-map trs))
       ;; :equations
       ;; ,(trs$eqns trs)
       ;; :transitions
       ;; ,(trs$trns trs)
       )
      ))

;;; ----------
;;;  SORT MAP
;;; ----------

(defun string-replace-space-with (name &optional (sup-str "_"))
  (declare (type simple-string name sup-str))
  (let ((nam-tok (parse-with-delimiter name #\space)))
    (if (cdr nam-tok)
        (reduce #'(lambda (x y)
                    (declare (type simple-string x y))
                    (concatenate 'string
                                 x
                                 sup-str
                                 y))
                nam-tok)
        (car nam-tok))))

(defun trs-proper-sort-p (sort)
  (or (sort= sort *sort-id-sort*)
      (not (or (err-sort-p sort)
               (memq (sort-module sort)
                     *kernel-hard-wired-builtin-modules*)))))

(defun trs-proper-sort-p* (sort)
  (or (sort= sort *sort-id-sort*)
      (not (memq (sort-module sort)
                 *kernel-hard-wired-builtin-modules*))))

;;;
;;;
;;;
;;; (defvar _trs_mod_name_hash_ (make-hash-table :test #'eqal))
(defvar _trs_mod_name_hash_ (make-hash-table :test #'eq))

(defun clear-trs-mod-name-hash ()
  (clrhash _trs_mod_name_hash_))

(eval-when (:execute :compile-toplevel :load-toplevel)
  (declaim (type fixnum _trs_module_name_))
  (defvar _trs_module_names_ 0)

  (defun make-trs-module-name-internal (name)
    (declare (ignore name))
    (format nil ".trs#~d." (incf _trs_module_names_)))
  )

(defun make-trs-module-name (module)
  (let ((name (module-name module)))
    (if (modexp-is-simple-name name)
        (make-module-print-name2 module)
        (or (gethash module _trs_mod_name_hash_)
            (let ((trs-nam (make-trs-module-name-internal name)))
              (setf (gethash module _trs_mod_name_hash_)
                    trs-nam)
              trs-nam)))))

(defun make-trs-sort-name (sort)
  (let* ((org-sort (get-original-sort sort))
         (dep-mod (sort-module org-sort)))
    (when (memq dep-mod *tram-builtin-modules*)
      (setq sort org-sort))
    (values 
     (intern (concatenate 'string
                          (string-replace-space-with
                           (the simple-string (string (sort-id sort)))
                           "$sp$")
                          "."
                          (the simple-string
                            (make-trs-module-name (sort-module sort)))))
     dep-mod
     )))

(defun make-sort-name-map (trs)
  (let ((so (trs$sort-order trs)))
    (dolist (sort (trs$sorts trs))
      (when (trs-proper-sort-p* sort)
        (push (cons sort (make-trs-sort-name sort))
              (trs$sort-name-map trs))
        (let ((ds (direct-supersorts sort so)))
          (when (and (null (cdr ds)) (err-sort-p (car ds))
                     (not (assq (car ds) (trs$sort-name-map trs))))
            (push (cons (car ds) (make-trs-sort-name (car ds)))
                  (trs$sort-name-map trs))))
        ))))

(defun map-chaos-sort-to-trs (sort trs)
  (cdr (assq sort (trs$sort-name-map trs))))

(defun map-chaos-sort-to-trs-or-panic (sort trs &optional ignore-error)
  (unless (sort-struct-p sort) (break "PANIC"))
  (or (map-chaos-sort-to-trs sort trs)
      (cond ((sort= sort *identifier-sort*)
             '|Id.QID|)                 ; just for a moment
            ((sort= sort *universal-sort*)
             (sort-name *universal-sort*))
            ((sort= sort *huniversal-sort*)
             (sort-name *huniversal-sort*))
            ((sort= sort *cosmos*)
             (sort-name *cosmos*))
            ((sort= sort *bottom-sort*)
             (sort-name *bottom-sort*))
            (t (if ignore-error
                   (sort-name sort)
                   (with-output-panic-message ()
                     (format t
                             "could not map sort ~a to trs"
                             (string (sort-id sort)))
                     nil))))))
                
(defun map-trs-sort-to-chaos (name trs)
  (when (stringp name)
    (setq name (intern name)))
  (or (car (rassoc name (trs$sort-name-map trs) :test #'eq))
      (if (eq name '|Id.QID|)
          *identifier-sort*
        nil)
      ))

;;; 
;;; SUBSORT RELATIONS
;;;
(defun make-trs-sort-graph (trs)
  (let ((so (trs$sort-order trs))
        ;; (snmlist (trs$sort-name-map trs))
        (sub-rel nil)
        (err-rel nil))
    (dolist (s (trs$sorts trs))
      (block next
        ;; (unless (trs-proper-sort-p s) (return-from next nil))
        (let ((supers (direct-supersorts s so)))
          (when supers
            (if (and (null (cdr supers))
                     (err-sort-p (car supers)))
                (if (not (trs-proper-sort-p s))
                    (return-from next nil)
                  (push (list (map-chaos-sort-to-trs-or-panic s trs)
                              (map-chaos-sort-to-trs-or-panic (car supers) trs))
                        err-rel))
              ;; else
              (let ((s-mapped (map-chaos-sort-to-trs-or-panic s trs t)))
                (setq supers
                      (delete-if-not #'(lambda (x)
                                         (trs-proper-sort-p x))
                                     supers))
                (unless supers
                  (return-from next nil))
                (dolist (sup supers)
                  (push (list s-mapped
                              (map-chaos-sort-to-trs-or-panic sup trs))
                        sub-rel))))))
        ))
    ;;
    (setf (trs$sort-graph trs) (nreverse sub-rel))
    (setf (trs$err-sorts trs) (nreverse err-rel))
    ))
  
;;; --------------
;;;  OPERATOR MAP
;;; --------------

;;; OPERATOR MAP
;;;   method -> (name arity coarity attribute ...)
;;; 

(defparameter trs-operator-special-token-map
  '(
    ;; (#\{ . "\\{")
    ;; (#\} . "\\}")
    (#\[ . "\\[")
    (#\] . "\\]")
    ;; (#\_ . "\\_")
    (#\( . "\\(")
    (#\) . "\\)")
    (#\, . "\\,")
    (#\space . "$sp$")))

(defvar *trs-opname-hash* (make-hash-table :test #'equal))

(defun clear-trs-opname-hash ()
  (clrhash *trs-opname-hash*))

(defun clear-trs-db ()
  (clear-trs-opname-hash)
  (clear-trs-mod-name-hash))

(defun trs-proper-method-p (meth)
  (and (not (method-is-error-method meth))
       (not (memq (method-module meth)
                  *kernel-hard-wired-builtin-modules*))
       (not (or (eq meth *bool-if*)
                (eq meth *sort-membership*)
                (eq meth *bool-equal*)
                (eq meth *beh-equal*)
                (eq meth *beh-eq-pred*)
                (eq meth *bool-nonequal*)
                (eq meth *rwl-predicate*)
                (eq meth *rwl-predicate2*)))))

;;;

(defvar *trs-modify-operator-name* t)

(defun trs-check-if-builtin-op-family (method opinfo-table)
  (or (eq method *bool-true-meth*)
      (eq method *bool-false-meth*)
      (let ((mxs (cons method (method-overloaded-methods method opinfo-table))))
        (some #'(lambda (x)
                  (let ((mmod (method-module x)))
                    (or (memq mmod *tram-bool-modules*)
                        (memq mmod *tram-builtin-modules*))))
              mxs))))

(defun trs-get-real-method-if-dummy (method trs)
  (let ((ent (rassoc method (trs$dummy-methods trs))))
    (if ent
        (caar ent)
        method)))

(defun make-trs-op-name (method module &aux (trs (module-trs module)))
  ;; NOTE* assumption: sort name map should have been generated.
  ;;       this is used for modifying operator name with the error-sort
  ;;       of its coarity.
  (let ((name (cadr (assq method (trs$op-info-map trs))))
        (opinfo-table (module-opinfo-table module))
        (sort-name-map (trs$sort-name-map trs)))
    (when name (return-from make-trs-op-name name))
    ;;
    (setq method (trs-get-real-method-if-dummy method trs))
    ;;
    (if (get-method-info method opinfo-table)
        (let ((op (method-operator method opinfo-table)))
          (setq name (operator-print-name op)))
        (let ((meth-name (method-name method)))
          (if (member "_" (car meth-name) :test #'equal)
              ;; mixfix
              (setq name (make-print-operator-id (car meth-name)))
              ;; 
              (setq name (format nil "~a/~d"
                                 (make-print-operator-id (car meth-name))
                                 (cdr meth-name))))))
    ;;
    (when (and *trs-modify-operator-name*
               (not (trs-check-if-builtin-op-family method opinfo-table)))
      (setq name (concatenate 'string
                              name
                              (let ((err-sort (the-err-sort (method-coarity method)
                                                            (module-sort-order module))))
                                (string (or (cdr (assq err-sort sort-name-map))
                                            (sort-id err-sort)))))))
    ;;
    (or (gethash name *trs-opname-hash*)
        (setf (gethash name *trs-opname-hash*)
              (let ((res nil)
                    (lim (length name))
                    (cur-tok nil))
                (declare (type fixnum lim))
                (do ((pos 0 (1+ pos)))
                    ((>= pos lim))
                  (declare (type fixnum pos))
                  (setq cur-tok (char name pos))
                  (push (or (cdr (assoc cur-tok
                                        trs-operator-special-token-map
                                        :test #'equal))
                            (string cur-tok))
                        res))
                (intern (reduce #'(lambda (x y)
                                    (declare (type simple-string x y))
                                    (concatenate 'string x y))
                                (nreverse res))))))))

(defun make-trs-op-info (method trs)
  (let ((module (trs$module trs)))
    (with-in-module (module)
      (let ((method-name (make-trs-op-name method module))
            (arity (mapcar #'(lambda (s) (map-chaos-sort-to-trs-or-panic s
                                                                         trs
                                                                         t))
                           (method-arity method)))
            (coarity (map-chaos-sort-to-trs-or-panic
                      (method-coarity method)
                      trs
                      t))
            (attrs (make-trs-method-attr method module)))
        (list* method-name arity coarity attrs)))))

(defun make-trs-op-maps (trs)
  (let ((module (trs$module trs)))
    (let ((res nil))
      ;; construct op mapping tables and reverse maps.
      ;; NOTE* only error operators are entried to reverse table
      ;;       excepting constants and built-in operators.
      ;;       (constants have no error-methods in general).
      ;;       most of the cases, constants need not be in rev-table
      ;;       but there are some cases to be handled properly, like
      ;;        op c : -> Elt.M1*{ ... }
      ;;        op c : -> Elt.M2*{ ... }
      ;;       the reason is that we generate internal trs names for
      ;;       modules with complex name, thus we could not recover
      ;;       original operator easily (we want to use standard procs for
      ;;       getting modules from their names).
      ;;
      (dolist (ops (module-all-operators module))
        (let ((methods (opinfo-methods ops)))
          (dolist (m methods)
            (let ((info (make-trs-op-info m trs)))
              (when (or (method-is-error-method m)
                        (null (method-arity m)))
                (let ((rev-ent (assq (car info)
                                     (trs$op-rev-table trs))))
                  (if rev-ent
                      (setf (cdr rev-ent) m)
                      (push (cons (car info) m)
                            (trs$op-rev-table trs)))))
              (when (trs-proper-method-p m)
                ;; trs-proper-method-p rejects error method.
                (push (cons m info) res))))))
      ;; make reverse op maps for builtin operators
      (when (assq *truth-module* (module-all-submodules module))
        (dolist (op (list *bool-equal* *bool-nonequal*
                          *sort-membership*
                          *beh-equal* *bool-if* *beh-eq-pred*))
          (push (cons (make-trs-op-name op module)
                      op)
                (trs$op-rev-table trs))))
      ;; other optional built-ins.
      #|| TODO: 
      (when (module-includes-rwl module)
        (push (cons (make-trs-op-name *rwl-predicate* module)
                    *rwl-predicate*)
              (trs$op-rev-table trs))
        (push (cons (make-trs-op-name *rwl-predicate2* module)
                    *rwl-predicate2*)
              (trs$op-rev-table trs)))
      ||#
      ;;
      (setf (trs$op-info-map trs)
            (nreverse res)))))

(defun make-trs-method-attr (meth module)
  (with-in-module (module)
    (let ((theory (method-theory meth))
          (strat (method-rewrite-strategy meth))
          (constr (method-constructor meth))
          ;; (prec (method-precedence meth))
          (assoc (method-associativity meth))
          (memo (method-has-memo meth))
          (res nil))
      ;;
      ;; (when (and (eql 0 (car (last strat)))
      ;;   (member 0 (butlast strat)))
      ;;   (setq strat (butlast strat)))
      ;;
      (let ((th-info (theory-info theory))
            (zero (theory-zero theory)))
        (when (not (eq th-info the-e-property))
          (when (or (theory-info-is-AC th-info)
                    (theory-info-is-A th-info)
                    (theory-info-is-AI th-info)
                    (theory-info-is-AZ th-info)
                    (theory-info-is-AIZ th-info)
                    (theory-info-is-ACI th-info)
                    (theory-info-is-ACZ th-info)
                    (theory-info-is-ACIZ th-info))
            (push ':assoc res))
          (when (or (theory-info-is-AC th-info)
                    (theory-info-is-C th-info)
                    (theory-info-is-CI th-info)
                    (theory-info-is-CZ th-info)
                    (theory-info-is-CIZ th-info)
                    (theory-info-is-ACI th-info)
                    (theory-info-is-ACZ th-info)
                    (theory-info-is-ACIZ th-info))
            (push ':comm res))
          (when (or (theory-info-is-I th-info)
                    (theory-info-is-IZ th-info)
                    (theory-info-is-CI th-info)
                    (theory-info-is-CIZ th-info)
                    (theory-info-is-AI th-info)
                    (theory-info-is-AIZ th-info)
                    (theory-info-is-ACI th-info)
                    (theory-info-is-ACIZ th-info))
            (push ':idem res))
          (when zero
            (let ((mth (car zero)))     ; to be fixed later.
              (if (null (cdr zero))
                  (push (list ':id mth) res)
                  (push (list ':idr mth) res))))
          ))
      (when strat
        (push (list ':strat strat) res))
      (when memo
        (push ':memo res))
      (when constr
        (push ':constr res))
      (when assoc
        (push (if (eq :left assoc)
                  ':l-assoc
                  ':r-assoc)
              res))
      res)))
  
(defun fix-trs-ids (trs)
  (dolist (map (trs$op-info-map trs))
    (let* ((info (cdr map))
           (zero (find-if #'(lambda (x) (and (consp x)
                                             (or (eq (car x) :id)
                                                 (eq (car x) :idr))))
                          info)))
      (when zero
        (setf (cdr zero) (list (trs$make-term-form (cadr zero) trs)))))))

(defun map-chaos-op-to-trs (method trs)
  (or (cadr (assq method (trs$op-info-map trs)))
      (make-trs-op-name method (trs$module trs))
      (with-output-panic-message ()
        (format t "cound not map operator ~a"
                (method-symbol method))
        (chaos-error 'panic))))

(defun map-chaos-op-to-trs-info (method trs)
  (cdr (assq method (trs$op-info-map trs))))

(defun trs-rev-op-name (name trs)
  (when (stringp name)
    (setq name (intern name)))
  (or (cdr (assq name (trs$op-rev-table trs)))
      (let* ((opnam (list (string name)))
             (opref (parse-op-name opnam))
             (opinfos (car (find-qual-operators opref (trs$module trs)))))
        (car (opinfo-methods opinfos)))
      (with-output-panic-message ()
        (format t "could not find reverse map of operator symbol ~a"
                name)
        (chaos-error 'panic))))

;;;
;;; BUILTIN OPERATORS
;;;
(defun find-trs-dummy-method (trs meth arity coarity)
  (cdr (assoc (list meth arity coarity)
              (trs$dummy-methods trs)
              :test #'equal)))

(defun make-trs-dummy-method (trs meth arity coarity)
  (or (find-trs-dummy-method trs meth arity coarity)
      (with-in-module ((trs$module trs))
        (let* ((op (method-operator meth))
               (new-meth (make-operator-method :name (operator-name op)
                                               :arity arity
                                               :coarity coarity)))
          (setf (method-constructor new-meth)
                (method-constructor meth))
          (setf (method-is-behavioural new-meth)
                (method-is-behavioural meth))
          (setf (method-module new-meth)
                *current-module*)
          (setf (method-supplied-strategy new-meth)
                (method-supplied-strategy meth))
          (setf (method-precedence new-meth)
                (method-precedence meth))
          (setf (method-associativity new-meth)
                (method-associativity meth))
          (push (cons (list meth arity coarity) new-meth)
                (trs$dummy-methods trs))
          ;;
          new-meth))))

(defun make-trs-builtin-bin-op-info (trs meth arity coarity)
  (let ((new-meth
         (make-trs-dummy-method trs meth arity coarity)))
    ;;
    (let ((info (make-trs-op-info meth trs))
          (r-arity (mapcar #'(lambda (x)
                               (map-chaos-sort-to-trs-or-panic x trs))
                           arity))
          (r-coarity (map-chaos-sort-to-trs-or-panic coarity trs)))
      (setf (second info) r-arity
            (third info) r-coarity)
      (cons new-meth info))))

(defun make-trs-if-then-else-info (trs sort)
  (let ((new-meth (make-trs-dummy-method trs
                                         *bool-if*
                                         (list *bool-sort* sort sort)
                                         sort))
        (info (make-trs-op-info *bool-if* trs))
        (bool (map-chaos-sort-to-trs-or-panic *bool-sort* trs))
        (s (map-chaos-sort-to-trs-or-panic sort trs))
        )
    (setf (second info) (list bool s s))
    (setf (third info) s)
    (cons new-meth info)))

(defun make-trs-if-then-else-axioms (trs sort)
  (let* ((var-then (make-variable-term sort 'THEN))
         (var-else (make-variable-term sort 'ELSE))
         (if-op (find-trs-dummy-method trs *bool-if*
                                       (list *bool-sort* sort sort)
                                       sort))
         (lhs-1 (make-applform sort
                               if-op
                               (list *bool-true* var-then var-else)))
         (lhs-2 (make-applform sort
                               if-op
                               (list *bool-false* var-then var-else)))
         (rhs-1 var-then)
         (rhs-2 var-else))
    (list (make-rule :lhs lhs-1 :rhs rhs-1 :condition *bool-true*
                     :type :equation
                     :no-method-computation t)
          (make-rule :lhs lhs-2 :rhs rhs-2 :condition *bool-true*
                     :type :equation
                     :no-method-computation t))
    ))

(defun get-trs-top-sorts (trs)
  (let ((top-sorts nil))
    (dolist (sort (maximal-sorts (trs$sorts trs)
                                 (trs$sort-order trs)))
      (when (trs-proper-sort-p sort)
        (push sort top-sorts)))
    top-sorts))

(defun get-trs-error-sorts (trs)
  (let ((error-sorts nil))
    (dolist (ent (trs$sort-name-map trs) error-sorts)
        (when (err-sort-p (car ent))
          (push (car ent) error-sorts)))))

(defun make-trs-biopinfos (trs sorts)
  (let ((infos nil)
        (axs nil))
    (dolist (sort sorts)
      (if (sort-is-hidden sort)
          (push (make-trs-builtin-bin-op-info trs *beh-equal*
                                              (list sort sort)
                                              *bool-sort*)
                infos)
          (progn
            ;; _==_
            (push (make-trs-builtin-bin-op-info trs *bool-equal*
                                                (list sort sort)
                                                *bool-sort*)
                  infos)
            ;; _=b=_
            (when (sort-is-hidden sort)
              (push (make-trs-builtin-bin-op-info trs *beh-eq-pred*
                                                  (list sort sort)
                                                  *bool-sort*)
                    infos))
            ;; _=*=_
            (when (sort-is-hidden sort)
              (push (make-trs-builtin-bin-op-info trs *beh-equal*
                                                  (list sort sort)
                                                  *bool-sort*)
                    infos))
            ;; _=/=_
            (push (make-trs-builtin-bin-op-info trs *bool-nonequal*
                                                (list sort sort)
                                                *bool-sort*)
                  infos)))
      ;; if_then_else_fi
      (push (make-trs-if-then-else-info trs sort)
            infos)
      (push (make-trs-if-then-else-axioms trs sort)
            axs)
      )
    ;;
    (values infos axs)
    ))

(defun make-trs-builtin-op-maps (trs)
  (let* ((mod (trs$module trs))
         (top-sorts nil)
         (rel-infos nil)
         (if-then-axs nil)
         )
    ;;
    (setq top-sorts (get-trs-top-sorts trs))
    ;;
    (when (assq *truth-module* (module-all-submodules mod))
      (multiple-value-bind (infos axs)
          (make-trs-biopinfos trs top-sorts)
        (setq rel-infos infos)
        (setq if-then-axs axs))
      )
    (when nil                           ; (or (eq *rwl-module* mod)
                                        ;     (assq *rwl-module* (module-all-submodules mod)))
      ;; _==>_
      (dolist (sort top-sorts)
        (unless (sort-is-hidden sort)
          (push (make-trs-builtin-bin-op-info trs
                                              *rwl-predicate*
                                              (list sort sort)
                                              *bool-sort*)
                rel-infos)
          (push (make-trs-builtin-bin-op-info trs
                                              *rwl-predicate2*
                                              (list sort
                                                    *rwl-nat-star-sort*
                                                    sort)
                                              *bool-sort*)
                rel-infos)
          )))
    ;;
    (when *on-trs-debug*
      (format t "~%sem-relations = ~A" rel-infos))
    ;;
    (setf (trs$sem-relations trs) rel-infos)
    (dolist (ax if-then-axs)
      (let ((ax1 (car ax))
            (ax2 (cadr ax)))
        (push ax1 (trs$sem-axioms trs))
        (push ax2 (trs$sem-axioms trs))))
    ))

;;; ------
;;;  TERM
;;; ------

(defmacro trs-term-type (term) `(car ,term))
(defmacro trs-term-head (term) `(cadr ,term))
(defmacro trs-term-builtin-value (term) `(cadr ,term))
(defmacro trs-term-sort (term) `(caddr ,term))
(defmacro trs-term-subterms (term) `(cdddr ,term))

(defun trs$make-term-form (term trs)
  (let ((res (trs$make-term-form* term trs)))
    (trs-set-if-then-sort res)
    res))

(defun trs-set-if-then-sort (res)
  (if (and (eq :op (trs-term-type res))
           (null (trs-term-sort res))
           (eq '|if_then_else_fi| (trs-term-head res)))
      (let ((sort (trs-get-if-then-sort res)))
        (setf (trs-term-sort res) sort)
        sort)
      (trs-term-sort res)))

(defun trs-get-if-then-sort (trs-term)
  (let ((arg2 (second (trs-term-subterms trs-term)))
        (sort nil))
    (setq sort (trs-term-sort arg2))
    (unless sort
      (with-output-panic-message ()
        (format t "could not set sort for if-then-else-fi!")
        (break)
        (chaos-error 'panic)))
    sort))
      
(defun trs$make-term-form* (term trs)      
  (cond ((term-is-simple-lisp-form? term)
         (list ':lisp (lisp-form-original-form term)))
        ((term-is-general-lisp-form? term)
         (list ':glisp (lisp-form-original-form term)))
        ((term-is-builtin-constant? term)
         (list :builtin-value
               (term-builtin-value term)
               (map-chaos-sort-to-trs (term-sort term) trs)))
        ((term-is-variable? term)
         (list :var (variable-name term)
               (map-chaos-sort-to-trs (variable-sort term) trs)))
        ((term-is-applform? term)
         (list* :op
                (map-chaos-op-to-trs (term-head term) trs)
                (map-chaos-sort-to-trs (term-sort term) trs)
                (mapcar #'(lambda (x)
                            (trs$make-term-form x trs))
                        (term-subterms term))))
        (t (with-output-panic-message ()
             (format t "unknown term : ")
             (term-print term)))))

(defun trs-term-variables (term)
  (case (trs-term-type term)
    (:var (list term))
    (:op (let ((res nil))
           (dolist (st (trs-term-subterms term) res)
             (setq res (union res (trs-term-variables st)
                              :test #'equal)))))
    (otherwise nil)))

(defun trs-re-make-term-form (trs trs-term)
  (with-in-module ((trs$module trs))
    (with-output-to-string (str)
      (let ((*standard-output* str))
        (re-print-trs-term trs trs-term parser-max-precedence)
        str))))

(defun re-print-trs-term (trs trs-term prec)
  (declare (type fixnum prec))
  (case (trs-term-type trs-term)
    (:var (princ (string (trs-term-head trs-term))))
    (:op (let ((op-name (trs-term-head trs-term)))
             (let ((hd (trs-rev-op-name op-name trs))
                   (op nil))
               (setq op (method-operator hd))
               (cond ((not (operator-is-mixfix op))
                      (let ((subs (trs-term-subterms trs-term)))
                        (format t "~{~a~^ ~}" (operator-symbol op))
                        (when subs
                          (princ "(")
                          (let ((flg nil))
                            (dolist (i subs)
                              (if flg (princ ",") (setq flg t))
                              (re-print-trs-term trs i parser-max-precedence)
                              ))
                          (princ ")"))))
                     (t (let ((prec-test (and (get-method-precedence hd)
                                              (<= prec
                                                  (get-method-precedence hd))))
                              (assoc-test (method-is-associative hd)))
                          (when prec-test (princ "("))
                          (let ((subs (trs-term-subterms trs-term))
                                (prv nil))
                            (dolist (i (operator-token-sequence op))
                              (cond
                                ((eq i t)
                                 (when prv (princ " "))
                                 (setq prv t)
                                 (let ((tm (car subs)))
                                   (re-print-trs-term
                                    trs
                                    tm
                                    (if (and assoc-test
                                             tm
                                             (eq :op (trs-term-type tm))
                                             (eq (trs-term-head tm)
                                                 (trs-term-head trs-term)))
                                        parser-max-precedence
                                        (or (get-method-precedence hd)
                                            0)))
                                   (setq subs (cdr subs))))
                                (t (when prv (princ " "))
                                   (setq prv t)
                                   (princ i)))))
                          (when prec-test (princ ")"))
                          ))))))
    (:builtin-value (princ (trs-term-head trs-term)))
    (otherwise (format t "!! not supported (~a)" trs-term)))
  )

;;; --------
;;;  AXIOMS
;;; --------

#||
(defun make-trs-axioms (trs)
  (let ((mod (trs$module trs)))
    (let ((own-axs (module-own-axioms-ordered mod nil))
          (imp-axs (module-imported-axioms mod nil))
          (eqns nil)
          (trns nil)
          (val nil))
      (setq val (trs$get-axioms own-axs trs))
      (setq eqns (car val)
            trns (cadr val))
      (setq val (trs$get-axioms imp-axs trs))
      (setf (trs$eqns trs) (nconc eqns (car val)))
      (setf (trs$trns trs) (nconc trns (cadr val))))))
||#

(defun trs$get-axioms (axs trs &optional include-bad-rule)
  (let ((eqs nil)
        (trns nil)
        (tinfo nil))
    (dolist (ax axs (list eqs trns))
      (let ((lhs-top (term-head (axiom-lhs ax))))
        (unless (or (eq lhs-top *bool-if*)
                    (eq lhs-top *bool-equal*)
                    (eq lhs-top *beh-eq-pred*)
                    (eq lhs-top *bool-nonequal*)
                    ;; (eq lhs-top *rwl-predicate*)
                    )
          (setq tinfo (get-trs-axiom ax trs include-bad-rule))
          (if (memq (axiom-type ax) '(:equation :pignose-axiom :pignose-goal))
              (push tinfo eqs)
              (push tinfo trns)))))
    ))

(defun get-trs-axiom (ax trs &optional include-bad-rule)
  (let* ((lhs (axiom-lhs ax))
         (rhs (axiom-rhs ax))
         (cond (axiom-condition ax))
         (condp (not (is-true? cond)))
         (type (axiom-type ax))
         (behavioural (axiom-is-behavioural ax))
         (kind (axiom-kind ax))
         (label (axiom-labels ax)))
    (when (eq kind :bad-rule)
      (unless include-bad-rule
        (return-from get-trs-axiom nil)))
    (list* (case type
             ((:equation :pignose-axiom :pignose-goal)
              (cond (behavioural
                     (cond (condp :bceq)
                           (t :beq)))
                    (t (cond (condp :ceq)
                             (t :eq)))))
             (t (cond (behavioural
                       (cond (condp :bctrans)
                             (t :btrans)))
                      (t (cond (condp :ctrans)
                               (t :trans))))))
           (if label
               (string (car label))
               nil)
           (trs$make-term-form lhs trs)
           (trs$make-term-form rhs trs)
           (if condp
               (list (trs$make-term-form cond trs))
               nil))))

(defmacro trs-axiom-type (ax) `(car ,ax))
(defmacro trs-axiom-label (ax) `(cadr ,ax))
(defmacro trs-axiom-lhs (ax) `(caddr ,ax))
(defmacro trs-axiom-rhs (ax) `(cadddr ,ax))
(defmacro trs-axiom-condition (ax) `(car (cddddr ,ax)))
(defun trs-axiom-is-built-in (x)
  (let ((type (trs-term-type (trs-axiom-rhs x))))
    (memq type '(:glisp :lisp))))

;;; EOF
