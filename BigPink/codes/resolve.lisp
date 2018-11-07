;;;-*-Mode:LISP; Package: CHAOS; Base:10; Syntax:Common-lisp -*-
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
;;;
(in-package :chaos)
#|=============================================================================
                             System:Chaos
                            Module:BigPink
                          File:resolve.lisp
=============================================================================|#
#-:chaos-debug
(declaim (optimize (speed 3) (safety 0) #-GCL (debug 0)))
#+:chaos-debug
(declaim (optimize (speed 1) (safety 3) #-GCL (debug 3)))

;;;                          ***********
;;;                           RESOLVERS
;;;                          ***********


;;; BUILD-HYPER
;;; - construct a hyper-resolvent
;;;
(declaim (inline comb-clash-subst))

(defun comb-clash-subst (giv-subst clash)
  (declare (type list giv-subst)
           (type (or null clash) clash))
  (if clash
      (let ((subst nil)
            (c clash))
        (loop (unless c (return))
          (let ((nsub (clash-subst c)))
            (if nsub
                (setq subst nsub)))
          (setq c (clash-next c)))
        (compose-subst giv-subst subst))
    giv-subst))

(defun build-hyper (clash given-subst nuc-lits nucleus giv-lits giv-sat inf-id nuc-pos)
  (declare (ignore nuc-pos)
           (type (or null clash) clash)
           (type list given-subst)
           (type list nuc-lits)
           (type clause nucleus)
           (type list giv-lits)
           (type (or null clause) giv-sat)
           (type symbol inf-id))
  (let ((new-literals nil)
        (new-clause (new-clause *current-psys*))
        (history nil)
        (subst nil)
        (clashes clash))
    (declare (type list new-literals)
             (type clause new-clause)
             (type list history subst)
             (type (or null clash) clashes))
    (setq subst
      (comb-clash-subst given-subst clash))
    (when (pn-flag debug-hyper-res)
      (format t "~%build-hyper: clash =")
      (prin1 clash)
      (print-next)
      (princ "givn-subst = ") (print-substitution given-subst)
      (print-next)
      (princ "cmb subst = ") (print-substitution subst))
    (when giv-sat
      ;; given clause is satellite
      (push (clause-id giv-sat) history))
    (push (clause-id nucleus) history)
    ;; construct literals of resolvent
    (dolist (lit giv-lits)
      (declare (type literal lit))
      (let ((new-literal (shallow-copy-literal lit new-clause)))
        (declare (type literal new-literal))
        (setf (literal-atom new-literal)
          (apply-subst subst (literal-atom lit)))
        (push new-literal new-literals)))
    (dolist (lit nuc-lits)
      (declare (type literal lit))
      (let ((new-literal (shallow-copy-literal lit new-clause)))
        (declare (type literal new-literal))
        (setf (literal-atom new-literal)
          (apply-subst subst (literal-atom lit)))
        (push new-literal new-literals)))
    (while clashes
      (if (clash-evaluable clashes)
          (push :eval history)
        (let* ((found-lit (clash-found-lit clashes))
               (sat-clause (literal-clause found-lit))
               )
          (declare (type literal found-lit)
                   (type clause sat-clause))
          (push (clause-id sat-clause) history)
          (dolist (lit (clause-literals sat-clause))
            (declare (type literal lit))
            (unless (eq lit found-lit)
              (let ((new-literal (shallow-copy-literal lit new-clause)))
                (declare (type literal new-literal))
                (setf (literal-atom new-literal)
                  ;; clash-subst?
                  (apply-subst subst (literal-atom lit))
                  ;; (apply-subst (clash-subst clashes) (literal-atom lit))
                  )
                (push new-literal new-literals))))
          (let ((junk-id (cdr (assq :dummy-clause
                                    (clause-attributes sat-clause)))))
            (when junk-id
              (delete-clause! junk-id *current-psys*))
            )))
      (setq clashes (clash-next clashes)))
    (setf (clause-literals new-clause)
      (nreverse new-literals))
    
    (setq history (cons inf-id (nreverse history)))
    (setf (clause-parents new-clause) (list history))
    (when (pn-flag debug-hyper-res)
      (format t "~%** build-hyper: new-clause =")
      (print-clause new-clause))
    new-clause))

;;; HYPER-CLASH! 
;;; - used by hyper and UR resolution to clash away the marked literals
;;;   of the given nucleus
;;; - append kept resolvents to *SOS*
;;;
;;; c-start : clash
;;; subst   : substitution
;;; nuc-lits: non-clahsed literals of the nucleus.
;;; nuc     : the nucleus.
;;; giv-lits: if the given clause is a satellite, these are its
;;;           non-clashed literals, else NIL.
;;; sat-proc: function to identify (other) satelites:
;;;           `positive-clause?' for hyper, `unit-clause?' for UR.
;;; inf-id  : one of :hyper, :neg-hyper, :ur, specifying the inference type.
;;; nuc-pos : if not nil, given clause is a satelite

(declaim (special _clash_so_far_)
         (type list _clash_so_far_))
(defvar _clash_so_far_ nil)

(declaim (inline rename-subst))

(defun rename-subst (subst var-map)
  (declare (type list subst var-map)
           (values list))
  (if subst
      (let ((res nil))
        (declare (list res))
        (dolist (s subst)
          (let ((bind (variable-image var-map (car s))))
            (declare (type (or null term) bind))
            (if bind
                (progn
                  (push (cons (car s) bind) res)
                  (when (term-is-variable? bind)
                    (push (cons bind
                                (apply-subst var-map (cdr s)))
                          res))
                  )
              (push (cons (car s)
                          (apply-subst var-map (cdr s)))
                    res))))
        (setq res (nreverse res))
        (dolist (vm var-map)
          (unless (variable-image res (car vm))
            (push vm res)))
        res)
    (if var-map
        var-map
      nil)))

(defun maximal-literal (l1)
  (declare (type literal l1)
           (values symbol))
  (flet ((opcompare (m1 m2)
           (declare (type method m1 m2))
           (if (method-w= m1 m2)
               nil
             (let ((p1 (method-lex-prec m1))
                   (p2 (method-lex-prec m2)))
               (declare (type fixnum p1 p2))
               (if (< p1 p2)
                   :less
                 nil)))))
    (let ((atom (literal-atom l1)))
      (declare (type term atom))
      (dolist (l2 (clause-literals (literal-clause l1)) t)
        (declare (type literal l2))
        (if (and (not (eq l1 l2))
                 (not (answer-literal? l2)))
            (if (and (positive-literal? l2)
                     (not (positive-literal? l1)))
                (return nil)
              (if (and (eq (literal-sign l1)
                           (literal-sign l2))
                       (eq :less
                           (opcompare (term-head atom)
                                      (term-head (literal-atom l2)))))
                  (return nil))))))))

(declaim (inline compose-subst2))

(defun compose-subst2 (s1 s2)
  (declare (type list s1 s2))
  (labels ((add-new (s newsl)
             (declare (type (or null term) s)
                      (type list newsl))
             (cond ((null s) newsl)
                   ((variable-image newsl (caar s))
                    (add-new (cdr s) newsl))
                   (t (cons (car s) (add-new (cdr s) newsl)))))
           (composel (s1 s2)
             (cond ((null s1) nil)
                   ;; !!!
                   ((variable-image s2 (caar s1))
                    (composel (cdr s1) s2))
                   (t (cons (cons (caar s1)
                                  (apply-subst s2 (cdar s1)))
                            (composel (cdr s1) s2))))))
    (if (car s2)
        (add-new s2 (composel s1 s2))
      s1)))

(declaim (inline cl-occurs-in-clash))
         
(defun cl-occurs-in-clash (clash-clause clash)
  (declare (type clause clash-clause)
           (type clash))
  (let ((clh clash))
    (declare (type (or null clash) clh))
    (loop
      (setq clh (clash-prev clh))
      (unless clh (return-from cl-occurs-in-clash nil))
      (when (and (clash-found-lit clh)
                 (eq (literal-clause (clash-found-lit clh))
                     clash-clause))
        (return-from cl-occurs-in-clash t))))
  nil)

(defun clash-one (clash clause-pred given-subst inf-id &optional giv-sat)
  (declare (type clash clash)
           (type list given-subst)
           (type symbol inf-id)
           (type (or null clause) giv-sat))
  (let ((clashables (if (clash-clashables clash)
                        (cdr (clash-clashables clash))
                      (setf (clash-clashables clash)
                        (is-fetch-concat (literal-atom (clash-literal clash))
                                         (clash-db clash)))))
        (atom (literal-atom (clash-literal clash)))
        (subst (if (clash-prev clash)
                   (or (get-nsubst (clash-prev clash))
                       given-subst)
                 given-subst)))
    (declare (type list clashables)
             (type term atom)
             (type list subst))
    (loop
      (unless clashables
        (return nil))
      (block next
        (let* ((lit-data (car clashables))
               (clash-lit lit-data)
               (clash-clause (literal-clause clash-lit))
               (junk-cl-id nil))
          (declare (type literal clash-lit)
                   (type clause clash-clause)
                   (type (or null fixnum) junk-cl-id))
          (when (and (funcall clause-pred clash-clause)
                     (or (not (pn-flag order-hyper))
                         (eq :ur-res-rule inf-id)
                         (maximal-literal clash-lit)))
            (let (;; (clash-atom (literal-entry-atom clash-lit))
                  (clash-atom (literal-atom clash-lit))
                  (varmap nil)
                  (natom atom))
              (declare (ignore varmap)
                       (type term clash-atom natom))
              (setq atom (apply-subst subst atom))
              (when (or (eq giv-sat clash-clause)
                        (cl-occurs-in-clash clash-clause clash))
                (unless (term-eq natom atom)
                  (multiple-value-bind (dcl tlit id)
                      (make-dummy-clause clash-clause
                                         clash-lit)
                    (declare (type clause dcl)
                             (type literal tlit)
                             (type fixnum id))
                    (setq junk-cl-id id)
                    (setq clash-lit tlit)
                    (setq clash-atom (literal-atom tlit))
                    (setq clash-clause dcl))))
              (when (pn-flag debug-hyper-res)
                (with-output-msg ()
                  (princ "chash-one trying unify:")
                  (print-next)
                  (format t "clash = ~s" (literal-clause (clash-literal clash)))
                  (print-next)
                  (princ "atom = ") (term-print atom)
                  (print-next)
                  (format t "target clause = ~s " clash-clause)
                  (print-next)
                  (princ "target atom = ") (term-print clash-atom)))
              (multiple-value-bind (new-subst no-match e-equal)
                  (unify clash-atom
                         atom
                         nil)
                (declare (type substitution new-subst)
                         (type (or null t) no-match)
                         (ignore e-equal))
                (when no-match
                  (when junk-cl-id
                    (delete-clause! junk-cl-id *current-psys*))
                  (return-from next nil))
                (if new-subst
                    (progn
                      (setq new-subst (compose-subst subst new-subst)))
                  (setq new-subst subst))
                (when (pn-flag debug-hyper-res)
                  (with-output-simple-msg ()
                    (princ "* clash-one success: ")
                    (princ "nuc = ") (print-clause
                                      (literal-clause
                                       (clash-literal clash)))
                    (print-next)
                    (princ "nuc atom = ") (term-print atom)
                    (print-next)
                    (princ "target(electron) = ") (term-print clash-atom)
                    (print-next)
                    (format t "target cl-id = ~D"
                            (clause-id clash-clause))
                    (print-next)
                    (princ "subst = ")
                    (print-substitution new-subst)
                    ))

                ;; success!
                (setf (clash-subst clash) new-subst)
                (setf (clash-clashables clash) clashables)
                (setf (clash-found-lit clash) clash-lit)
                (return-from clash-one t)))))) ; block next
      ;; try next clashable
      (setq clashables (cdr clashables))) ; end loop
    nil))

(defun get-nsubst (clashes)
  (if (null clashes)
      nil
    (or (clash-subst clashes)
        (get-nsubst (clash-prev clashes)))))

(defun hyper-clash! (c-start
                     given-subst
                     nuc-lits
                     nuc
                     giv-lits
                     giv-sat
                     sat-proc
                     inf-id
                     nuc-pos)
  (declare (type (or null clash) c-start)
           (type list given-subst)
           (type list nuc-lits)
           (type (or null clause) nuc)
           (type list giv-lits)
           (type (or null clause) giv-sat)
           (type symbol inf-id)
           (type (or null fixnum) nuc-pos))
  (let ((clashes nil)
        (list-resolvent nil)
        (backup nil)
        (c-end nil))
    (declare (type (or null clash) clashes)
             (type list list-resolvent)
             (type (or null clash) c-end))
    (loop
      (if (not backup)
          (if (or (null c-start)
                  (and clashes
                       (null (clash-next clashes))))
              ;; clash is complete
              (let ((resolvent nil))
                (setq resolvent (build-hyper c-start ; clash list
                                             given-subst
                                             nuc-lits ; non-clash lits of nucleus
                                             nuc ; nucleus clause
                                             giv-lits
                                             giv-sat
                                             inf-id
                                             nuc-pos))
                (case inf-id
                  (:hyper-res-rule
                   (incf (pn-stat hyper-res-gen)))
                  (:neg-hyper-res-rule
                   (incf (pn-stat neg-hyper-res-gen)))
                  (otherwise
                   (incf (pn-stat ur-res-gen))))
                (incf (pn-stat cl-generated))
                ;; pre-process the hyper-resolvent
                (when (pre-process resolvent nil :sos)
                  (push resolvent list-resolvent))
                (setq backup t)
                (setq c-end clashes)    ; the last success clash 
                (setq clashes nil))
            ;; else
            (progn
              (if (null clashes)        ; just starting
                  (setq clashes c-start)
                ;; try next clash
                (setq clashes (clash-next clashes)))
              (when (clash-evaluable clashes)
                (let* ((lit (clash-literal clashes))
                       (atom (literal-atom lit))
                       (subst (get-nsubst clashes))
                       (inst nil))
                  (unless subst (setq subst given-subst))
                  (setq inst (demod-atom (apply-subst subst atom)))
                  (if (positive-literal? lit)
                      (setf (clash-evaluation clashes)
                        (is-false? inst))
                    (setf (clash-evaluation clashes)
                      (is-true? inst)))
                  (setf (clash-already-evaluated clashes) nil)))
              ;; initialize clashsable list
              (setf (clash-clashables clashes) nil)))
        ;;
        ;; else backup
        ;;
        (if (or (null c-start)          
                (and clashes
                     (null (clash-prev clashes))))
            ;; done with this nucleus
            (return-from hyper-clash! list-resolvent)
          ;; else
          (progn
            (if (null clashes)
                (progn
                  (setq clashes c-end)  ; restart from the
                                        ; last successed clash
                  )
              ;; else
              ;; back track to previous one.
              (progn
                (setf (clash-clashables clashes) nil)
                (setq clashes (clash-prev clashes))))
            ;; try again
            (unless (clash-evaluable clashes)
              (setf (clash-subst clashes) nil))
            (setq backup nil))))
      (unless backup
        (if (clash-evaluable clashes)
            (if (or (clash-already-evaluated clashes)
                    (not (clash-evaluation clashes)))
                (setq backup t)
              ;; set flag and proceed
              (setf (clash-already-evaluated clashes) t))
          (unless (clash-one clashes sat-proc given-subst inf-id giv-sat)
            (setq backup t)))))         ; loop end
    ;; done
    list-resolvent))

;;; (positive) HYPER RESOLUTION
;;;
;;; - append kept resolvents to *SOS*
;;; - each kept clause has already passed to the pre-process filter
;;;   (forward subsumption, etc.), inserted into appropriate indexes.
;;;
(defun hyper-resolution (clause)
  (declare (type clause clause))
  (when (= (the fixnum (num-literals clause)) 0)
    (return-from hyper-resolution nil))
  (let ((resolvent-list nil)
        (given-literals nil)
        (clash-start nil)
        (last-clash nil)
        (nuc-literals nil)
        (nuc-pos 0))
    (declare (type list resolvent-list)
             (type list given-literals)
             (type (or null clash) clash-start)
             (type (or null clash) last-clash)
             (type list nuc-literals)
             (type fixnum nuc-pos))
    (when (pn-flag debug-hyper-res)
      (with-output-simple-msg ()
        (princ "Start[hyper-resolution]:")
        (print-next)
        (print-clause clause)))
    (cond
     ((not (positive-clause? clause))
      ;; given clause is nucleus,i.e, contains at least one
      ;; negative literal
      (setq clash-start nil
            last-clash nil
            nuc-literals nil)
      (dolist (lit (clause-literals clause))
        (cond ((or (positive-literal? lit) (answer-literal? lit))
               (push lit nuc-literals))
              (t (let ((new-clash (make-clash :literal lit
                                              :db *clash-pos-literals*)))
                   (declare (type clash new-clash))
                   (if (null clash-start)
                       (setq clash-start new-clash)
                     (progn
                       (setf (clash-prev new-clash) last-clash)
                       (setf (clash-next last-clash) new-clash)))
                   (when (method-is-meta-demod (term-head (literal-atom lit)))
                     (setf (clash-evaluable new-clash) t))
                   (setq last-clash new-clash)))))
      (let ((res (hyper-clash! clash-start
                               nil      ; subst
                               nuc-literals
                               clause
                               nil
                               nil
                               #'positive-clause?
                               :hyper-res-rule
                               nil)))
        (when res
          (setq resolvent-list (nconc res resolvent-list)))))
     (t
      ;; given clause is a satellite.
      (dolist (l3 (clause-literals clause))
        (declare (type literal l3))
        (when (or (not (pn-flag order-hyper))
                  (maximal-literal l3))
          (setq given-literals nil)
          (dolist (lit (clause-literals clause))
            (declare (type literal lit))
            (unless (eq l3 lit)
              (push lit given-literals)))
          (let ((clashables
                 (is-fetch-concat (literal-atom l3) *clash-neg-literals*)))
            (dolist (lit-data clashables)
              (block next
                (let* ((nuc-lit lit-data)
                       (nuc (literal-clause (the literal nuc-lit))))
                  (when (not (positive-clause? nuc))
                    (multiple-value-bind (new-subst no-match e-equal)
                        (unify (literal-atom l3)
                               (literal-atom nuc-lit)
                               nil)
                      (declare (ignore e-equal)
                               (type list new-subst))
                      (when no-match (return-from next)) ; try next 
                      ;; found a nucleus
                      (setq nuc-literals nil)
                      (setq clash-start nil
                            last-clash nil)
                      (let ((i 0))
                        (declare (type fixnum i))
                        (dolist (lit (clause-literals nuc))
                          (declare (type literal lit))
                          (cond ((eq nuc-lit lit)
                                 (setq nuc-pos i))
                                ((or (positive-literal? lit)
                                     (answer-literal? lit))
                                 (push lit nuc-literals))
                                (t
                                 ;; negative literal, put into clash structure
                                 (let ((new-clash (make-clash :literal lit
                                                              :db *clash-pos-literals*)))
                                   (declare (type clash new-clash))
                                   (if (null clash-start)
                                       (setq clash-start new-clash)
                                     (progn
                                       (setf (clash-prev new-clash)
                                         last-clash)
                                       (setf (clash-next last-clash)
                                         new-clash)))
                                   (when (method-is-meta-demod
                                          (term-head (literal-atom lit)))
                                     (setf (clash-evaluable new-clash) t))
                                   (setq last-clash new-clash))))))
                      ;;
                      (let ((res (hyper-clash! clash-start
                                               new-subst
                                               nuc-literals
                                               nuc
                                               given-literals
                                               clause
                                               #'positive-clause?
                                               :hyper-res-rule
                                               nuc-pos)))
                        (when res
                          (setq resolvent-list (nconc res
                                                      resolvent-list)))
                        )))))           ; block next
              ))                        ; done for all possible clash
          ))                            ; done for all literals
      ))                                ; end conditions
    ;; done
    (when (pn-flag debug-hyper-res)
      (with-output-simple-msg ()
        (princ "End[hyper-res]")
        (print-next)
        (pr-clause-list resolvent-list)))
    (nreverse resolvent-list)))

;;; NEGATIVE HYPER RESOLUTION
;;; neg-hyper-resolution
;;; -- append kept resolvents to *SOS*
;;; -- each kept clause has already passed the pre-process filter
;;;    (forward subsumtion, etc.), been integrated and inserted into
;;;    appropriate indexes.
;;;
(defun neg-hyper-resolution (clause)
  (declare (type clause clause))
  (when (= (the fixnum (num-literals clause)) 0)
    (return-from neg-hyper-resolution nil))
  (let ((resolvent-list nil)
        (given-literals nil)
        (clash-start nil)
        (last-clash nil)
        (nuc-literals nil)
        (nuc-pos 0))
    (declare (type list resolvent-list)
             (type list given-literals)
             (type (or null clash) clash-start)
             (type (or null clash) last-clash)
             (type list nuc-literals)
             (type fixnum nuc-pos))
    (when (pn-flag debug-hyper-res)
      (with-output-simple-msg ()
        (princ "Start[neg-hyper-resolution]:")
        (print-next)
        (print-clause clause)))
    (cond
     ((not (negative-clause? clause))   ; given clause is nucleus
      ;; given clause is nucleus,i.e, contains at least one
      ;; positive literal
      (setq clash-start nil
            last-clash nil
            nuc-literals nil)
      (dolist (lit (clause-literals clause))
        (declare (type literal lit))
        (cond ((or (negative-literal? lit) (answer-literal? lit))
               (push lit nuc-literals))
              ;; put positive literal into clash structure
              (t (let ((new-clash (make-clash :literal lit
                                              :db *clash-neg-literals*)))
                   (declare (type clash new-clash))
                   (if (null clash-start)
                       (setq clash-start new-clash)
                     (progn
                       (setf (clash-prev new-clash) last-clash)
                       (setf (clash-next last-clash) new-clash)))
                   (when (method-is-meta-demod (term-head (literal-atom lit)))
                     (setf (clash-evaluable new-clash) t))
                   (setq last-clash new-clash)))))
      (let ((res (hyper-clash! clash-start
                               nil      ; subst
                               nuc-literals
                               clause
                               nil
                               nil
                               #'negative-clause?
                               :neg-hyper-res-rule
                               nil)))
        (when res
          (setq resolvent-list (nconc res resolvent-list)))))
     ;; given clause is a sattelite.
     (t 
      (dolist (l3 (clause-literals clause))
        (declare (type literal l3))
        (when (or (not (pn-flag order-hyper))
                  (maximal-literal l3))
          (setq given-literals nil)
          (dolist (lit (clause-literals clause))
            (declare (type literal lit))
            (unless (eq l3 lit)
              (push lit given-literals)))
          (let ((clashables
                 (is-fetch-concat (literal-atom l3) *clash-pos-literals*)))
            (dolist (lit-data clashables)
              (block next
                (let* (;; (nuc-lit (literal-entry-literal lit-data))
                       (nuc-lit lit-data)
                       (nuc (literal-clause (the literal nuc-lit))))
                  (when (not (negative-clause? nuc))
                    (multiple-value-bind (new-subst no-match e-equal)
                        (unify (literal-atom l3)
                               (literal-atom nuc-lit)
                               nil)
                      (declare (ignore e-equal)
                               (type list new-subst))
                      (when no-match (return-from next)) ; try next 
                      ;; found a nucleus
                      (setq nuc-literals nil)
                      (setq clash-start nil
                            last-clash nil)
                      (let ((i 0))
                        (declare (type fixnum i))
                        (dolist (lit (clause-literals nuc))
                          (declare (type literal lit))
                          (cond ((eq nuc-lit lit)
                                 (setq nuc-pos i))
                                ((or (negative-literal? lit)
                                     (answer-literal? lit))
                                 (push lit nuc-literals))
                                (t
                                 ;; pos literal, put into clash structure
                                 (let ((new-clash (make-clash :literal lit
                                                              :db *clash-neg-literals*)))
                                   (declare (type clash new-clash))
                                   (if (null clash-start)
                                       (setq clash-start new-clash)
                                     (progn
                                       (setf (clash-prev new-clash)
                                         last-clash)
                                       (setf (clash-next last-clash)
                                         new-clash)))
                                   (when (method-is-meta-demod
                                          (term-head (literal-atom lit)))
                                     (setf (clash-evaluable new-clash) t))
                                   (setq last-clash new-clash))))))
                      ;;
                      (let ((res (hyper-clash! clash-start
                                               new-subst
                                               nuc-literals
                                               nuc
                                               given-literals
                                               clause
                                               #'negative-clause?
                                               :neg-hyper-res-rule
                                               nuc-pos)))
                        (when res
                          (setq resolvent-list (nconc res
                                                      resolvent-list)))
                        )))))           ; block next
              ))                        ; done for all possible clash
          ))                            ; done for all literals
      ))
    ;; done
    (when (pn-flag debug-hyper-res)
      (with-output-simple-msg ()
        (princ "End[neg-hyper-res]")
        (print-next)
        (pr-clause-list resolvent-list)))
    (nreverse resolvent-list)))

;;; UNIT RESULTING RESOLUTION
;;; ur-resolution
;;; - append kept resolvents to *SOS*
;;; - each kept clause has already passed the pre-process filter
;;;   (forward subsumption, etc.), been itegrated, and inserted into 
;;;   appropreate indexes.
;;;
(defun ur-resolution (clause)
  (let ((num-lits 0)
        (resolvent-list nil)
        (given-literals nil)
        (clash-start nil)
        (last-clash nil)
        (nuc-literals nil)
        (nuc-pos 0))
    (setq num-lits (num-literals clause))
    (when (= 0 num-lits)
      (return-from ur-resolution nil))
    (cond ((> num-lits 1)               ; given clause is nucleus
           (setq clash-start nil        ; i.e., non-unit clause
                 last-clash nil
                 nuc-literals nil)
           (dolist (lit (clause-literals clause))
             (declare (type literal lit))
             (cond ((answer-literal? lit)
                    (push lit nuc-literals))))
           ;; setup nlits - 1 empty clash nodes
           (dotimes (x (1- num-lits))
             (let ((new-clash (make-clash)))
               (if (null clash-start)
                   (setq clash-start new-clash)
                 (progn
                   (setf (clash-prev new-clash) last-clash)
                   (setf (clash-next last-clash) new-clash)))
               (setq last-clash new-clash)))
           (dolist (box (clause-literals clause))
             (unless (answer-literal? box)
               (push box nuc-literals)
               (let ((c1 clash-start))
                 (dolist (lit (clause-literals clause))
                   (when (and (not (eq lit box)) (not (answer-literal? lit)))
                     (setf (clash-literal c1) lit)
                     (setf (clash-db c1) (if (positive-literal? lit)
                                             *clash-neg-literals*
                                           *clash-pos-literals*))
                     (setq c1 (clash-next c1))))
                 (when c1
                   (with-output-panic-message ()
                     (princ "ur-res: too many clash nodes (nuc).")))
                 (let ((res (hyper-clash! clash-start
                                          nil ; subst
                                          nuc-literals
                                          clause
                                          nil
                                          nil
                                          #'unit-clause?
                                          :ur-res-rule
                                          nil)))
                   (when res
                     (setq resolvent-list (nconc res resolvent-list))))
                 (pop nuc-literals))))) ; end of case nucleus
          (t                            ; given clause is satellite (unit).
           ;; collect any answer literal from given satellite
           ;; and get clashable literal (l3).
           (let ((l3 nil))
             (dolist (lit (clause-literals clause))
               (if (not (answer-literal? lit))
                   (setq l3 lit)        ; the only non-answer literal
                 (progn
                   (push lit given-literals))))
             (let ((clashables
                    (is-fetch-concat (literal-atom l3)
                                     (if (positive-literal? l3)
                                         *clash-neg-literals*
                                       *clash-pos-literals*))))
               (dolist (lit-data clashables)
                 (block next
                   (let* ((nuc-lit lit-data)
                          (nuc (literal-clause nuc-lit))
                          (nlits (num-literals nuc))
                          (new-subst nil)
                          (no-match nil)
                          (e-equal nil))
                     (when (> nlits 1)
                       (multiple-value-setq (new-subst no-match e-equal)
                         (unify (literal-atom l3)
                                (literal-atom nuc-lit)
                                nil))
                       (when no-match (return-from next)) ; try next
                       ;; found a nucleus
                       (setq nuc-literals nil)
                       (setq clash-start nil
                             last-clash nil)
                       ;; put answer literal into nuc-literals
                       (dolist (lit (clause-literals nuc))
                         (when (answer-literal? lit)
                           (push lit nuc-literals)))
                       ;; build clash structure for this nucleus
                       ;; nlits - 2 empty clash nodes
                       (dotimes (x (- nlits 2))
                         (let ((new-clash (make-clash)))
                           (if (null clash-start)
                               (setq clash-start new-clash)
                             (progn
                               (setf (clash-prev new-clash) last-clash)
                               (setf (clash-next last-clash) new-clash)))
                           (setq last-clash new-clash))
                         )
                       (dolist (box (clause-literals nuc))
                         (let ((j 1)
                               (c1 nil))
                           ;; if not clashed or answer literal
                           (when (and (not (eq box nuc-lit))
                                      (not (answer-literal? box)))
                             (setq c1 clash-start)
                             (push box nuc-literals)
                             (dolist (lit (clause-literals nuc))
                               (when (and (not (eq lit box))
                                          (not (eq lit nuc-lit))
                                          (not (answer-literal? lit)))
                                 (setf (clash-literal c1) lit)
                                 (setf (clash-db c1) (if (positive-literal? lit)
                                                         *clash-neg-literals*
                                                       *clash-pos-literals*))
                                 (setq c1 (clash-next c1))
                                 (incf j))
                               (when (eq lit nuc-lit)
                                 (setq nuc-pos j)))
                             (unless (null c1)
                               (princ c1)
                               (break "aho!")
                               (with-output-panic-message ()
                                 (princ "ur-res: too many clash nodes (sat).")))
                             (let ((res (hyper-clash! clash-start
                                                      new-subst
                                                      nuc-literals
                                                      nuc
                                                      given-literals
                                                      clause
                                                      #'unit-clause?
                                                      :ur-res
                                                      nuc-pos)))
                               (when res
                                 (setq resolvent-list
                                   (nconc res resolvent-list)))
                               ;;
                               (pop nuc-literals)))))
                       )))              ; block next
                 ))                     ; done for all possible clash
             )                          ; end case of satelite
           ))
    (nreverse resolvent-list)))
                             

;;; BUILD-BIN-RES : Literal1 Literal2 Subst -> Clause
;;; - construct a binary resolvent.
;;; - Literal1 and Literal2 are the clashed literals, and Subst
;;;   is a respective unifying substitutions.
;;;
(defun build-bin-res (l1 l2 subst &optional prop)
  (declare (type literal l1 l2)
           (type list subst))
  (let ((new-literals nil)
        (new-clause (new-clause *current-psys*)))
    (declare (type list new-literals)
             (type clause new-clause))
    (flet ((make-bin-res (literal)
             (declare (type literal literal))
             (dolist (lit (clause-literals (literal-clause literal)))
               (declare (type literal lit))
               (let ((new-literal nil))
                 (declare (type (or null literal) new-literal))
                 (unless (eq literal lit)
                   (setq new-literal (shallow-copy-literal lit new-clause))
                   (setf (literal-atom new-literal)
                     (apply-subst subst (literal-atom lit)))
                   (push new-literal new-literals))))))
      (make-bin-res l1)
      (make-bin-res l2)
      (setf (clause-literals new-clause) new-literals)
      (setf (clause-parents new-clause)
        (list (list (if prop
                        :pbinary-res-rule
                      :binary-res-rule)
                    (clause-id (literal-clause l1))
                    (clause-id (literal-clause l2)))))
      new-clause)))
       
;;; BINARY RESOLUTION
;;; binary-resolution
;;;
(defun binary-resolution (clause &optional prop-res?)
  (declare (type clause clause)
           (values list))
  (when (pn-flag debug-binary-res)
    (with-output-msg ()
      (princ "Start[binary-res]:")
      (print-next)
      (print-clause clause)))
  (let ((resolvent-list nil))
    (declare (type list resolvent-list))
    (dolist (lit (clause-literals clause))
      (declare (type literal lit))
      (block next
        (when prop-res?
          (unless (propositional-literal? lit)
            (return-from next nil)))
        (cond ((answer-literal? lit)
               ;; answer literal -- not yet
               )
              (t (let ((atom (literal-atom lit))
                       (db (if (positive-literal? lit)
                               ;; positive
                               *clash-neg-literals*
                             ;; negative
                             *clash-pos-literals*)))
                   (declare (type term atom)
                            (type hash-table db))
                   (let (;; (clashes (get-literal-entry-from-atom db atom))
                         (clashes (is-fetch-concat atom db))
                         (resolvent nil)
                         (in-subst nil))
                     (dolist (lit-data clashes)
                       (declare (type literal lit-data))
                       (let (;; (clash-atom (literal-entry-atom lit-data))
                             (clash-atom (literal-atom lit-data))
                             )
                         (multiple-value-bind (new-subst no-match e-equal)
                             (if prop-res?
                                 (prop-unify atom clash-atom)
                               (unify atom clash-atom in-subst))
                           (declare (ignore e-equal)
                                    (type list new-subst))
                           (unless no-match
                             (when (pn-flag debug-binary-res)
                               (with-output-simple-msg ()
                                 (format t "** binary-res:(prop-res = ~a )"
                                         (if prop-res? t nil))
                                 (print-next)
                                 (princ "atom = ")
                                 (term-print atom)
                                 (print-next)
                                 (format t "clash = ")
                                 (print-clause (literal-clause
                                                lit-data
                                                ))
                                 (print-next)
                                 (princ "subst = ")
                                 (print-substitution new-subst)))
                             (setq resolvent
                               (build-bin-res lit
                                              ;; (literal-entry-literal lit-data)
                                              lit-data
                                              new-subst
                                              prop-res?))
                             ;; (setq in-subst new-subst)
                             (incf (pn-stat cl-generated))
                             (incf (pn-stat binary-res-gen))
                             #|| NOT YET
                             (when (heat-is-on)
                               (setf (clause-heat-level resolvent)
                                 (1+ (clause-heat-level clause))))
                             ||#
                             (let ((pre-res nil))
                               (setq pre-res (pre-process resolvent nil :sos))
                               (when pre-res
                                 (push resolvent resolvent-list)))))))))))
        )                               ; block next
      )                                 ; end do
    ;;
    (when (pn-flag debug-binary-res)
      (with-output-msg ()
        (princ "End[binary-res]")
        (dolist (x (reverse resolvent-list))
          (print-next)
          (print-clause x))))
    (nreverse resolvent-list)))

;;; =========
;;; FACTORING
;;; =========

(defstruct (factor)
  (clause nil :type (or null clause))
  (l1p nil :type list)
  (l2p nil :type list))

;;; FIRST-FACTOR (clause)
;;;
(defun next-factor (f-struct)
  (declare (type factor f-struct))
  (let ((factored nil)
        (a-factor nil)
        (subst nil)
        (no-match nil)
        (e-eq nil))
    (declare (type (or null clause) a-factor)
             (type list subst))
    (setq factored
      (block found
        (do ((l1 (car (factor-l1p f-struct))
                 (car (factor-l1p f-struct))))
            ((null l1) (return-from found nil))
          (declare (type (or null literal) l1))
          (setf (factor-l2p f-struct) (cdr (factor-l2p f-struct)))
          (do ((l2 (car (factor-l2p f-struct))
                   (car (factor-l2p f-struct))))
              ((null l2))
            (declare (type (or null literal) l2))
            (if (eq (literal-sign l1) (literal-sign l2))
                (progn
                  (multiple-value-setq (subst no-match e-eq)
                    (unify (literal-atom l1)
                           (literal-atom l2)
                           nil))
                  (if no-match
                      (setf (factor-l2p f-struct)
                        (cdr (factor-l2p f-struct)))
                    ;; found a factor
                    (return-from found t)))
              (setf (factor-l2p f-struct)
                (cdr (factor-l2p f-struct)))))
          (setf (factor-l1p f-struct) (cdr (factor-l1p f-struct)))
          (setf (factor-l2p f-struct) (factor-l1p f-struct)))
        ;; failed
        nil))
    (when factored
      (let* ((lit2 (car (factor-l2p f-struct))) ; clause to be excluded
             (clause (factor-clause f-struct)))
        (declare (type literal lit2)
                 (type clause clause))
        (setq a-factor
          (cl-unique-variables
           (copy-clause (make-clause-shallow-copy clause (list lit2))
                        *current-psys*
                        #'(lambda (lit)
                            (declare (type literal lit))
                            (let ((new-lit
                                   (copy-literal lit
                                                 nil
                                                 ;; new-vars-list
                                                 nil
                                                 subst)))
                              (declare (type literal new-lit))
                              (when (test-bit (literal-stat-bits lit)
                                              oriented-eq-bit)
                                (set-bit (literal-stat-bits new-lit)
                                         oriented-eq-bit))
                              new-lit)))))))
    (when (pn-flag debug-infer)
      (when a-factor
        (with-output-simple-msg ()
          (princ "*FACTOR: ")
          (print-clause a-factor))))
    a-factor))

;;; GET-FACTORS : Clause -> List[Clause]
;;; generate factors from Clause
;;;
(defun get-factors (clause)
  (declare (type clause clause))
  (let ((factors nil))
    (declare (type list factors))
    (do* ((lits (clause-literals clause) (cdr lits))
          (lit1 (car lits) (car lits)))
        ((null (cdr lits)))
      (declare (type list lits)
               (type literal lit1))
      (dolist (lit2 (cdr lits))
        (declare (type literal lit2))
        (when (eq (literal-sign lit1) (literal-sign lit2))
          (multiple-value-bind (subst no-match e-eq)
              (unify (literal-atom lit1) (literal-atom lit2))
            (declare (ignore e-eq)
                     (type list subst))
            (unless no-match
              (let ((a-factor (make-clause-shallow-copy clause
                                                        (list lit2))))
                (declare (type clause a-factor))
                (setq a-factor (copy-clause
                                a-factor
                                *current-psys*
                                #'(lambda (lit)
                                    (let ((new-lit (copy-literal
                                                    lit
                                                    nil
                                                    nil
                                                    subst)))
                                      (when (test-bit (literal-stat-bits lit)
                                                      oriented-eq-bit)
                                        (set-bit (literal-stat-bits new-lit)
                                                 oriented-eq-bit))
                                      new-lit))))
                (push (cl-unique-variables a-factor) factors)))))))
    (nreverse factors)))

;;; ALL-FACTORS
;;; generate and pre-process all binary factors clause.
;;;
(defun all-factors (clause list)
  (declare (type clause clause)
           (type symbol list))
  (let ((factors (get-factors clause)))
    (declare (type list factors))
    (dolist (a-factor factors)
      (declare (type clause a-factor))
      (setf (clause-parents a-factor)
        (list (list :factor-rule (clause-id clause))))
      (incf (pn-stat cl-generated))
      (incf (pn-stat factor-gen))
      (pre-process a-factor nil list))))

;;; FACTOR-SIMPLIFY : Clause -> fixnum
;;;
(defun factor-simplify (clause)
  (declare (type clause clause)
           (values (or null fixnum)))
  (let ((f-struct (make-factor :clause clause
                               :l1p (clause-literals clause)
                               :l2p (clause-literals clause)))
        (num 0)
        (a-factor nil))
    (declare (type fixnum num)
             (type factor f-struct)
             (type (or null clause) a-factor))
    (setq a-factor (next-factor f-struct))
    (loop (unless a-factor (return))
      (if (subsume? a-factor clause)
          (let ((f-lits (clause-literals a-factor))
                (c-lits (clause-literals clause)))
            (declare (type list f-lits c-lits))
            (incf num)
            ;; swap literals
            (setf (clause-literals a-factor) c-lits)
            (setf (clause-literals clause) f-lits)
            (dolist (l (clause-literals a-factor))
              (setf (literal-clause l) a-factor))
            (dolist (l (clause-literals clause))
              (setf (literal-clause l) clause))
            (setf (clause-parents clause)
              (nconc (clause-parents clause)
                     (list (list :factor-simp-rule))))
            (delete-clause a-factor *current-psys*)
            (setf (factor-l1p f-struct) (clause-literals clause)
                  (factor-l2p f-struct) (clause-literals clause))
            (setq a-factor (next-factor f-struct)))
        (progn
          (delete-clause a-factor *current-psys*)
          (setq a-factor (next-factor f-struct)))))
    num ))


;;; EOF
