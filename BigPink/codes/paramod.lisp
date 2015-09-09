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
;;;
(in-package :chaos)
#|=============================================================================
                            System:Chaos
                           Module:BigPink
                           File:infer.lisp
=============================================================================|#
#-:chaos-debug
(declaim (optimize (speed 3) (safety 0) #-GCL (debug 0)))
#+:chaos-debug
(declaim (optimize (speed 1) (safety 3) #-GCL (debug 3)))

;;;============================================================================
;;;                 paramodulation inference rules
;;;============================================================================

(declaim (inline get-term-at))

(defun get-term-at (pos term)
  (declare (type list pos)
           (type term term)
           (values term))
  (let ((sub term))
    (declare (type term sub))
    (dolist (p (reverse pos))
      (declare (type fixnum p))
      (setq sub (term-arg-n sub p)))
    sub))

#||
(defun apply-subst-2 (sigma atom target-term beta)
  (declare (type list sigma)
           (type term atom target-term beta))
  (if (term-eq atom target-term)
      (apply-subst sigma beta)
    (cond ((term-is-variable? atom)
           (let ((im (variable-image sigma atom)))
             (if im                     ; i.e. im = sigma(term)
                 (values im t)
               (values atom nil))))
          ((term-is-builtin-constant? atom) atom)
          ((term-is-constant? atom)
           (if (term-eq atom target-term)
               (apply-subst sigma beta)
             (apply-subst sigma atom)))
          ((term-is-application-form? atom)
           (let ((l-result nil)
                 (modif-sort nil))
             (declare (type list l-result))
             (dolist (s-t (term-subterms atom))
               (multiple-value-bind (image-s-t same-sort)
                   (apply-subst-2 sigma s-t target-term beta)
                 (declare (type term image-s-t))
                 (unless same-sort
                   ;; (update-lowest-parse s-t)
                   (setq modif-sort t))
                 (push image-s-t l-result)))
             (setq l-result (nreverse l-result))
             (if modif-sort
                 (let ((term-image
                        (make-term-with-sort-check (term-head atom)
                                                   l-result)))
                   (values term-image
                           (sort= (term-sort atom)
                                  (term-sort term-image))))
               (values (make-applform (term-sort atom)
                                      (term-head atom)
                                      l-result)
                       t))))
          (t (with-output-panic-message ()
               (princ "apply-subst: encoutered illegual term")
               (terpri)
               (term-print atom)))))
  )
||#

(defun apply-subst-2 (sigma atom target-term beta target-pos &optional arg-pos)
  (declare (type list sigma)
           (type term atom target-term beta))
  (cond ((equal target-pos arg-pos)
         (apply-subst sigma beta))
        ((term-is-variable? atom)
         (let ((im (variable-image sigma atom)))
           (if im
               (values im t)
             (values atom nil))))
        ((term-is-builtin-constant? atom) atom)
        ((term-is-constant? atom)
         (apply-subst sigma atom))
        ((term-is-application-form? atom)
         (let ((l-result nil)
               (modif-sort nil))
           (let ((pos 0))
             (dolist (s-t (term-subterms atom))
               (multiple-value-bind (image-s-t same-sort)
                   (apply-subst-2 sigma s-t target-term beta 
                                  target-pos
                                  (cons pos arg-pos))
                 (unless same-sort
                   (setq modif-sort t))
                 (push image-s-t l-result)
                 (incf pos)))
             (setq l-result (nreverse l-result))
             (if modif-sort
                 (let ((term-image
                        (make-term-with-sort-check (term-head atom)
                                                   l-result)))
                   (values term-image
                           (sort= (term-sort atom)
                                  (term-sort term-image))))
               (values (make-applform (term-sort atom)
                                      (term-head atom)
                                      l-result)
                       t)))))
        (t (with-output-panic-message ()
             (princ "apply-subst: encoutered illegual term")
             (terpri)
             (term-print atom)))))


;;; BUILD-BIN-PARA
;;; construct paramodulant
;;;
(defun build-bin-para (rule target-term into-lit subst arg-pos)
  (declare (type paramod rule)
           (type term target-term)
           (type literal into-lit)
           (type list subst)
           (values clause))
  (let ((beta (paramod-rhs rule))
        (from-lit (paramod-literal rule))
        (into-clause (literal-clause into-lit))
        (new-literals nil)
        (new-clause (new-clause *current-psys*)))
    (declare (type term beta)
             (type literal from-lit)
             (type clause into-clause new-clause)
             (type list new-literals))
    (when (or (pn-flag debug-para-into)
              (pn-flag debug-para-from))
      (with-output-msg ()
        (princ "build-bin-para:")
        (print-next)
        (princ "target-term=")(term-print target-term)
        (print-next)
        (princ "subst=") (print-substitution subst)
        (print-next)
        ))
    
    ;; into clause
    (dolist (l (clause-literals into-clause))
      (declare (type literal l))
      (let ((new-atom nil)
            (new-literal (shallow-copy-literal l new-clause)))
        (declare (type literal new-literal)
                 (type (or null term) new-atom))
        (if (eq l into-lit)
            (setq new-atom (apply-subst-2 subst
                                          (literal-atom l)
                                          target-term
                                          beta
                                          arg-pos))
          (setq new-atom (apply-subst subst (literal-atom l))))
        (setf (literal-atom new-literal) new-atom)
        (mark-literal new-literal)
        (push new-literal new-literals)))
    ;; from clause
    (dolist (l (clause-literals (literal-clause from-lit)))
      (declare (type literal l))
      (unless (eq l from-lit)
        (let ((new-atom nil)
              (new-literal (shallow-copy-literal l new-clause)))
          (setq new-atom (apply-subst subst (literal-atom l)))
          (setf (literal-atom new-literal) new-atom)
          (mark-literal new-literal)
          (push new-literal new-literals))))
    ;;
    (setf (clause-literals new-clause) (nreverse new-literals))
    (when (or (pn-flag debug-para-into)
              (pn-flag debug-para-from))
      (with-output-msg ()
        (princ "build-bin-pra: new clause=")
        (print-clause new-clause)))
    ;;
    ;; (register-clause new-clause *current-psys*)
    new-clause
    ))

;;; PARA-INTO-TERMS-ALPHA
;;;
(defun para-into-terms-alpha (para-rule term lit &optional arg-pos)
  (declare (type paramod para-rule)
           (type term term)
           (type literal lit)
           (list arg-pos)
           (values list))
  (let ((paras nil))
    (declare (type list paras))
    (when (term-is-application-form? term)
      (cond ((eq (term-head term) *fopl-eq*)
             (when (pn-flag para-into-left)
               (setq paras
                 (nconc paras
                        (para-into-terms-alpha para-rule
                                               (term-arg-1 term)
                                               lit
                                               (cons 0 arg-pos)
                                               ))))
             (when (pn-flag para-into-right)
               (setq paras
                 (nconc paras
                        (para-into-terms-alpha para-rule
                                               (term-arg-2 term)
                                               lit
                                               (cons 1 arg-pos)
                                               ))))
             (return-from para-into-terms-alpha paras))
            ;;
            (t (let ((pos 0))
                 (declare (type fixnum pos))
                 (dolist (sub-t (term-subterms term))
                   (setq paras
                     (nconc paras
                            (para-into-terms-alpha para-rule
                                                   sub-t
                                                   lit
                                                   (cons pos arg-pos))))
                   (incf pos))))
            ))
    #||
    (when (term-is-application-form? term)
      (let ((pos 0))
        (declare (type fixnum pos))
        (dolist (sub-t (term-subterms term))
          (setq paras
            (nconc paras
                   (para-into-terms-alpha para-rule
                                          sub-t
                                          lit
                                          (cons pos arg-pos))))
          (incf pos))))
    ||#
    ;;
    ;; HEY!
    ;;
    (when (term-is-variable? term)
      (unless (pn-flag para-into-vars)
        (return-from para-into-terms-alpha nil)))
    ;;
    (let ((lhs (paramod-lhs para-rule))
          (p-lit (paramod-literal para-rule))
          (in-subst nil)
          (paramod nil)
          (same nil)
          (junk-cl-id nil))
      (declare (ignore same)
               (type term lhs)
               (type literal p-lit)
               (type list in-subst)
               (type (or null clause) paramod)
               (type (or null fixnum) junk-cl-id))
      ;; **
      (when (eq (literal-clause p-lit)
                (literal-clause lit))
        ;; (setq same t)
        (multiple-value-bind (new-cl llit id)
            (make-dummy-clause (literal-clause lit) lit)
          (declare (ignore new-cl))
          (setq junk-cl-id id)
          (setq lit llit)
          (setq term (literal-atom lit))
          (when arg-pos
            (setq term (get-term-at arg-pos term)))
          ))
      ;;
      ;; (trace unify)
      ;;
      (multiple-value-bind (new-subst no-match e-equal)
          (unify lhs term in-subst)
        (declare (ignore e-equal))
        (if no-match
            (when junk-cl-id
              (delete-clause! junk-cl-id *current-psys*))
          (progn
            ;; *******
            #||
            (when same
              ;; *****:
              (with-output-msg ()
                (princ "TAAAAAAAAAAAAAAA!!!!")
                (print-next)
                (format t "from paramod: ~a" para-rule)
                (print-next)
                (format t "target cl : ")
                (print-clause (literal-clause lit))
                (print-next)
                (format t "target term : ")
                (term-print (literal-atom lit))
                )
              ;; (setf (pn-flag debug-para-from) t)
              )
            ||#
            ;; *****
            
            (when (pn-flag debug-para-from)
              (with-output-msg ()
                (princ "para-from: success with rule =")
                (prin1 para-rule)
                (print-next)
                (princ "from clause   : ") (print-clause (literal-clause p-lit))
                (print-next)
                (princ "target clause : ") (print-clause (literal-clause lit))
                (print-next)
                (princ "target literal: ") (prin1 lit)))
            (setq paramod (build-bin-para para-rule term lit new-subst
                                          arg-pos))
            (when junk-cl-id
              (delete-clause! junk-cl-id *current-psys*))
            (setf (clause-parents paramod)
              (list (list :para-from-rule
                          (clause-id (literal-clause p-lit))
                          (clause-id (literal-clause lit)))))
            ;;
            (incf (pn-stat cl-generated))
            (incf (pn-stat para-from-gen))
            (let ((pre-res nil))
              (setq pre-res (pre-process paramod nil :sos))
              (when pre-res
                (setq paras
                  (nconc paras (list paramod)))))
            ))))
    ;;;
    ;;; (setf (pn-flag debug-para-from) nil)
    ;; (untrace unify)
    ;;;
    paras))
      
;;; PARA-FROM-ALPHA
;;;
(defun para-from-alpha (para-rule from-lit)
  (declare (type paramod para-rule)
           (type literal from-lit)
           (values list))
  (let ((list-para nil)
        (lhs (paramod-lhs para-rule)))
    (declare (type list list-para))
    (dolist (cl (if (term-is-variable? lhs)
                    *usable*
                  (get-clashable-clauses-from-atom *clash-lit-table*
                                                   lhs)))
      (declare (type clause cl))
      (when (or (not (pn-flag para-from-units-only))
                (unit-clause? cl))
        (dolist (lit (clause-literals cl))
          (unless (eq lit from-lit)
            (let ((atom (literal-atom lit)))
              (setq list-para
                (nconc list-para
                       (para-into-terms-alpha para-rule atom lit))))
            )
          )
        ))
    list-para
    ))

;;; PARAMODULATION-FROM
;;; - binary paramodulation from the given clause
;;; - paramodulants are given to `pre-process'.
;;;
(defun paramodulation-from (clause)
  (declare (type clause clause)
           (values list))
  (let ((paras nil))
    (declare (type list paras))
    (when (or (pn-flag debug-infer)
              (pn-flag debug-para-from))
      (with-output-msg ()
        (princ "Begin[paramod-from]:")))
    (when (or (not (pn-flag para-from-units-only))
              (unit-clause? clause))
      (dolist (from-lit (clause-literals clause))
        (declare (type literal from-lit))
        (block next
          (let ((atom (literal-atom from-lit)))
            (declare (type term atom))
            (when (and (positive-eq-literal? from-lit)
                       (not (term-is-identical (term-arg-1 atom)
                                               (term-arg-2 atom))))
              (let ((para-rule (make-paramod :literal from-lit)))
                (declare (type paramod para-rule))
                (when (pn-flag para-from-left)
                  (when (term-is-variable? (term-arg-1 atom))
                    (unless (pn-flag para-from-vars)
                      (return-from next nil)))
                  (setf (paramod-lhs para-rule) (term-arg-1 atom)
                        (paramod-rhs para-rule) (term-arg-2 atom))
                  (setq paras
                    (nconc paras
                           (para-from-alpha para-rule from-lit))))
                (when (pn-flag para-from-right)
                  (when (term-is-variable? (term-arg-2 atom))
                    (unless (pn-flag para-from-vars)
                      (return-from next nil)))
                  (setf (paramod-lhs para-rule) (term-arg-2 atom))
                  (setf (paramod-rhs para-rule) (term-arg-1 atom))
                  (setq paras
                    (nconc paras
                           (para-from-alpha para-rule from-lit))))))
            ))                          ; block next
        )                               ; dolist
      )
    ;;
    (when (or (pn-flag debug-infer)
              (pn-flag debug-para-from))
      (with-output-msg ()
        (princ "End[paramod-from]:")))
    paras))

;;; PARA-INTO-TERMS
;;; 
(defun para-into-terms (target-term into-lit &optional arg-pos)
  (declare (type term target-term)
           (type literal into-lit)
           (type list arg-pos)
           (values list))
  (let ((paras nil))
    (declare (type list paras))
    (when (term-is-application-form? target-term)
      #||
      (let ((pos 0))
        (declare (type fixnum pos))
        (dolist (sub-t (term-subterms target-term))
          (setq paras
            (nconc paras
                   (para-into-terms sub-t
                                    into-lit
                                    (cons pos arg-pos))))
          (incf pos)))
      ||#
      (cond ((eq (term-head target-term) *fopl-eq*)
             (when (pn-flag para-into-left)
               (setq paras
                 (nconc paras (para-into-terms (term-arg-1 target-term)
                                               into-lit
                                               ;; arg-pos ; '(0)
                                               (cons 0 arg-pos)
                                               ))))
             (when (pn-flag para-into-right)
               (setq paras
                 (nconc paras (para-into-terms (term-arg-2 target-term)
                                               into-lit
                                               ;; arg-pos ; '(1)
                                               (cons 1 arg-pos)
                                               ))))
             (return-from para-into-terms paras))
            ;;
            (t (let ((pos 0))
                 (declare (type fixnum pos))
                 (dolist (sub-t (term-subterms target-term))
                   (setq paras
                     (nconc paras
                            (para-into-terms sub-t
                                             into-lit
                                             (cons pos arg-pos))))
                   (incf pos))))
            )
      )
    #||
    (when (and (term-is-variable? target-term)
               (not (pn-flag para-into-vars)))
      (return-from para-into-terms nil))
    ||#
    (when (pn-flag debug-para-into)
      (with-output-msg ()
        (princ "para-into-terms: target=")
        (term-print target-term)))
    ;;
    (dolist (para-rule
                #||
              (append (get-literal-entry-from-atom *paramod-rules*
                                                     target-term)
                        (if (pn-flag para-from-vars)
                            (get-literal-entry-from-atom *paramod-rules*
                                                         (term-sort 
                                                          target-term)))
                        nil)
              ||#
              (is-paramod-fetch-concat target-term *paramod-rules*)
              )
      (declare (type paramod para-rule))
      (block next

        (when (pn-flag debug-para-into)
          (with-output-simple-msg ()
            (princ "para-into: rule = ")
            (princ para-rule)))

        (let* ((lhs (paramod-lhs para-rule))
               (from-lit (paramod-literal para-rule))
               (in-subst nil)
               (paramod nil)
               (same nil)
               (obso-cl-id nil))
          (declare (ignore in-subst)
                   (type term lhs)
                   (type literal from-lit)
                   (type list in-subst)
                   (type (or null clause) paramod)
                   (ignore same)
                   (type (or null fixnum) obso-cl-id))
          #||
          (when (term-eq lhs target-term)
            (return-from next nil))
          ||#
          ;; ***
          (when (eq (literal-clause into-lit)
                    (literal-clause from-lit))
            ;; (setq same t)
            (multiple-value-bind (new-cl llit cl-id)
                (make-dummy-clause (literal-clause into-lit) into-lit)
              (declare (ignore new-cl)
                       (type literal llit)
                       (type fixnum cl-id))
              (setq into-lit llit)
              (setq obso-cl-id cl-id)
              (setq target-term (literal-atom into-lit))
              (when arg-pos
                (setq target-term (get-term-at arg-pos target-term))
                ))
            )
          ;; ***
          ;; (trace unify)
          (multiple-value-bind (new-subst no-match e-equal)
              (unify lhs target-term nil)
            (declare (ignore e-equal)
                     (type list new-subst))
            (when no-match
              (when obso-cl-id
                (delete-clause! obso-cl-id *current-psys*))
              (return-from next nil))
            ;;
            #||
            (when same
              ;; ***
              (with-output-msg ()
                (princ "HAAAAAAAAAAAAAAAAA!!!!!!")
                (print-next)
                (format t "paramod : ~a" para-rule)
                (print-next)
                (format t "into : ")
                (print-clause (literal-clause into-lit))
                (print-next)
                (format t "target term : ")
                (term-print (literal-atom into-lit))
                )
              ;; (setf (pn-flag debug-para-into) t)
              )
            ||#
            ;; ***

            (when (pn-flag debug-para-into)
              (with-output-msg ()
                (format t "para-into-terms: matched p-rule = ")
                (pr-paramod para-rule))
              )
            (setq paramod
              (build-bin-para para-rule target-term into-lit new-subst arg-pos))
            (when obso-cl-id
              (delete-clause! obso-cl-id *current-psys*))
            (setf (clause-parents paramod)
              (list (list :para-into-rule
                          (clause-id (literal-clause into-lit))
                          (clause-id (literal-clause from-lit)))))
            ;;
            (incf (pn-stat cl-generated))
            (incf (pn-stat para-into-gen))
            (let ((pre-res nil))
              (setq pre-res (pre-process paramod nil :sos))
              (when pre-res
                (setq paras
                  (nconc paras (list paramod)))))
            ))))
    ;; :::
    ;;    (setf (pn-flag debug-para-into) nil)
    ;; (untrace unify)
    ;; :::
    paras))

;;; PARAMODULATION INTO
;;; - binary paramodulation into the given clause
;;; - paramodulants are given to `pre-process'.
;;;
(defun paramodulation-into (clause)
  (declare (type clause clause)
           (values list))
  (let ((list-para nil))
    (declare (type list list-para))
    (when (or (not (pn-flag para-into-units-only))
              (unit-clause? clause))
      ;;
      (when (or (pn-flag debug-infer)
                (pn-flag debug-para-into))
        (with-output-msg ()
          (format t "Start[paramodulation-into]: ")))
      ;;
      (dolist (into-lit (clause-literals clause))
        (declare (type literal into-lit))
        (block next
          (unless (answer-literal? into-lit)
            (let ((atom (literal-atom into-lit)))
              (setq list-para
                (nconc list-para
                       (para-into-terms atom into-lit))))))))
    ;;
    (when (or (pn-flag debug-infer)
              (pn-flag debug-para-into))
      (with-output-msg ()
        (format t "End[para-into]:")
        (print-next)
        (pr-clause-list list-para t)))
    ;;
    list-para
    ))

;;; EOF
