;;;-*- Mode:Lisp; Syntax:CommonLisp; Package: CHAOS -*-
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
                                  System:Chaos
                                 Module:e-match
                               File:match-ac.lisp
==============================================================================|#

#-:chaos-debug
(declaim (optimize (speed 3) (safety 0) #-GCL (debug 0)))

#+:chaos-debug
(declaim (optimize (speed 1) (safety 3) #-(or GCL EXCL) (debug 3)
                   #+EXCL (debug 2)))

;;; PROCEDURES for AC Matching ================================================

;;;; Version as of April, 1990 incorporating TW's 2 bug fixes,
;;;; and various 'improvements' by PDL.
;;;;
;;;; All the functions for AC matching in the OBJ3 system.
;;;;
;;;; Patrick Lincoln, March 1989 - April 1990, 
;;;  SRI Declarative Languages Project, CSL, SRI.
;;;
;;; The basic structure of the representation is taken from:
;;; ``Adventures In Associative-Commutative Unification''
;;; Patrick Lincoln and Jim Christian, from the 
;;; {\em Journal of Symbolic Computation}.
;;; The basic idea is to represent the terms in an AC system of equations
;;; as vectors of bit-vectors (integers), (a virtual boolean matrix) which 
;;; represents the state of the AC system.  
;;;
;;; For the moment, there will be no HZ symetry check.  (because 
;;; conditional rewrite rules might invalidate the check, and I
;;; can't figure out how to find out if a rule is conditional from
;;; inside the AC proc.)
;;;
;;; Modification History:
;;; June 1989: first working version.  Many small fixes, improvements.
;;; July 13, 1989: PDL adds a GCD failure check.
;;; July-August 1989: PDL uses TW's performance meter to find slow code.
;;;                   Lots of small performance mods.  
;;;                   Some of TW's C code used in place of dotimes, etc.
;;; January 2 1990: PDL wakes up, and realizes that to handle systems of
;;;                 multiple equations, he can use compatibility bitvectors,
;;;                 eliminating the old way of just calling AC recursively.
;;;
;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;;;
;;; the following interface-definitions have not changed from CK+TW's OBJ3.
;;; pdl will not flame at length here on the relative merits of this interface.

; op AC$state_initialize: System Environment -> ACState, signals(no_match)
; op AC$next_state: ACState -> System ACState, signals(no_more)
; op AC$equal: Term Term -> Bool
; op AC$unparse_AC_state: ACState -> Output

;;; the general plan is to 
;;; 1> initialize the system, by changing the representation of terms.
;;; 2> simplify the equation by tossing matching terms from both sides, 
;;;    and noting the repetitions and duplicates.
;;; 3> detect trivial cases, one variable on LHS, constant remaining on LHS
;;; 4> build matrix
;;; 5> solve matrix
;;; 6> construct solution from matrix
;;;
;;; The most time consuming will be 1, because the
;;; term-representation ensures tests for e-equality are expensive.
;;; 2 is definately worthwhile.  Perhaps more simplification could be done.
;;; 3 may or may not be worthwhile, but it is implemented.
;;; 4 is simply (make-array X :initial element 1)
;;; 5 is essentially search, but pdl turned it into counting (by rotation)
;;; 6 isn't pretty, but not too costly.
;;; 
;;; Note that the representation used here (bitvectors) have remarkably
;;; non differentiable performance curves, the step at 31 bits notable
;;; among its features.  Thus if lots of rules have more than 31 terms
;;; (under the top level AC function symbol, and after simplification)
;;; this will perform poorly.  However, there can be any number of terms
;;; in the RHS (actuals), and if there are less than 32 terms then
;;; this should be nice and fast.
;;;
;;; Representation:  c=constant, f=functional term, v=variable
;;;     After simplification, where duplicates (terms appearing on both
;;;     sides of equation) are removed, we build a matrix:
;;;
;;;
;;;               LHS
;;;         c      f     v
;;;       ___________________
;;;     |
;;;    c|  a       b      c
;;;     |
;;; R   |  
;;; H  f|  d       e      f
;;; S   |
;;;     | 
;;;    v|  g       h      i
;;;
;;;
;;; g,h,i are disallowed because we are doing matching, and the
;;;       RHS is assumed ground.
;;; a,d are disallowed because once we have simplified, any constant
;;;     left on the LHS has nothing to match.
;;; b is disallowed because funs never match constants.
;;; That leaves c,e,f.
;;; 
;;; Since i do not group equal terms together, the rows and columns of
;;; this matrix are filled with ones and zeros.  (instead of arbitrary ints)
;;; Then search is performed by moving bits instead of moving ints.
;;;
;;; c is represented by a one dimensional array (sv) of bitvectors.  
;;; e,f are represented by another one dimensional array of bitvectors.  
;;;     (e and f are concatinated together, essentially).
;;;
;;; Note is made of repeated terms and of compatibility between LHS and
;;; RHS function symbols (I know this is O(N^2), but returning flocks of
;;; unsolvable systems is worse than spending a few microseconds 
;;; computing the "match$possibly_matches" once and for all.)
;;; These notes are used to aviod redundant search, and are kept in
;;; several auxilliary vectors.
;;;
;;;            LHS
;;;       f f f | v v v v
;;;       1 2 3 | 1 2 3 4
;;;   ___________________
;;;   c1        | 0 0 0 1
;;;   c2        | 0 0 1 0
;;;   c3   NO   | 1 0 0 0
;;;R  c4        | 0 1 0 0
;;;H  c5        | 0 0 1 0
;;;S  -------------------
;;;   f1  0 0 1 | 0 0 0 0
;;;   f2  1 0 0 | 0 0 0 0
;;;   f3  0 1 0 | 0 0 0 0
;;;   f4  0 0 0 | 0 1 0 0
;;;
;;; Above is a sample solution matrix
;;;  From this the solution is read downward through the rows:
;;;  lv1=rc3, lv2=op(rc4,rf4), lv3=op(rc2,rc5), lv4=rc1
;;;  lf1=rf2, lf2=rf3, lf3=rf1, 
;;;
;;; NO means that no ones are allowed in this region.
;;;
;;; For small efficiency gains, the bounds on the matrix are stored 
;;; instead of recomputed.
;;; 
;;; Detail:
;;; This scheme needs to be modified for repeated variables.
;;; First, the repetition of every variable, function, and constant
;;; is noted in a vector.  Then only things with enough duplicates
;;; may have a 1 in a repeted column.  Finally, when returning the
;;; solution (system of equations), ignore all but one of the repeated
;;; variables or terms.
;;;
;;; Detail:
;;; For each RHS function a compatibility vector is built by testing
;;; match$possibly_matches against each LHS function.  This is stored
;;; in the compatibility vector, which also contains information from
;;; the repetitions.
;;;
;;; Implementation note:  For now, only AC matching is implemented.  
;;; ACZ and ACI equations are not handled, although PDL thinks they
;;; could be without too much pain.
;;;

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;;; 
;;; PDL's fault from here on in.
;;;
;;;
;;; Implementation note: KCL structures are poorly implemented, both in 
;;; construction time (huge) and in space (2x reasonable).
;;; Thus PDL implements AC-state on his own.
#|
(defstruct AC-state
  operators                             ; array[op]
                                        ; the top level operators of each eqn in the system
  LHS-f                                 ; array[term] functional terms
  LHS-v                                 ; array[term] variables
  RHS-c                                 ; array[term] constants 
  RHS-f                                 ; array[term] functional terms
  LHS-f-r                               ; array[bool] notes repeated functional terms
  LHS-v-r                               ; array[bool] notes repeated variables
  RHS-c-r                               ; array[bool] notes repeated constants
  RHS-f-r                               ; array[bool] notes repeated functional terms
  (LHS-mask 0)                          ; long int variables and funs accounted
                                        ; for by RHS-c-sol
  (LHS-f-mask 0)                        ; long int funs accounted for by RHS-c-sol
  (LHS-r-mask 0)                        ; long int bitvector of all repeated (>0)
                                        ; terms on lhs
  RHS-c-sol                             ; array[int] solution matrix; constants
  RHS-c-max                             ; int ; max value of elements of RHS-c-sol
  RHS-f-sol                             ; array[int] solution matrix; functional terms
  RHS-f-max                             ; int max value of elements of RHS-f-sol
  RHS-full-bits                         ; int 11111...111               
  RHS-c-compat                          ; array[int] array of compatibility bitvectors
  RHS-f-compat                          ; array[int] array of compatibility bitvectors
  LHS-c-count                           ; int number of constants on LHS
                                        ; after simplification
  LHS-f-count                           ; int number of functions on LHS
                                        ; after simplification
  LHS-v-count                           ; int number of variables on LHS
                                        ; after simplification
  RHS-c-count                           ; int number of constants on RHS
                                        ; after simplification
  RHS-f-count                           ; int number of functions on RHS
                                        ; after simplification
  RHS-f-match-top-ac                    ; array[bool] can that term match the top op? (nil)
  (no-more nil)                         ; when true implies that all solutions
                                        ; have been reported
  )
|#
(defmacro make-AC-state ()  `(alloc-svec 26))

;;; the toplevel operators of each equation in the system
;;; type : array[term]
(defmacro AC-state-operators (____state) `(svref ,____state 0))

;;; functional terms
;;; type : array[term]
(defmacro AC-state-lhs-f (____state) `(svref ,____state 1))

;;; variables on the LHS
;;; type : array[term]
(defmacro AC-state-lhs-v (____state) `(svref ,____state 2))

;;; contants on the RHS
;;; type : array[term]
(defmacro AC-state-rhs-c (____state)  `(svref ,____state 3))

;;; functional terms on RHS
;;; type : array[term]
(defmacro AC-state-rhs-f (____state)  `(svref ,____state 4))

;;; notes repeated functional terms of LHS
;;; type : array[bool]
(defmacro AC-state-lhs-f-r (____state)  `(svref ,____state 5))

;;; notes repeated variables of LHS
;;; type : array[bool]
(defmacro AC-state-lhs-v-r (____state)  `(svref ,____state 6))

;;; notes repeated constants of RHS
;;; type : array[bool]
(defmacro AC-state-rhs-c-r (____state)  `(svref ,____state 7))

;;; notes repreated funcational terms of RHS
;;; type : array[bool]
(defmacro AC-state-rhs-f-r (____state)  `(svref ,____state 8))

;;; variables and funs acocunted for by RHS-c-sol
;;; type : fixnum
(defmacro AC-state-lhs-mask (____state)  `(svref ,____state 9))

;;; funs accounted for by RHS-c-sol
;;; type : fixnum
(defmacro AC-state-lhs-f-mask (____state)  `(svref ,____state 10))

;;; bit vector of all repeated (> 0) terms on LHS
(defmacro AC-state-lhs-r-mask (____state)  `(svref ,____state 11))

;;; solution matrix for constants
;;; type : array[fixnum]
(defmacro AC-state-rhs-c-sol (____state)  `(svref ,____state 12 ))

;;; max value of elements of RHS-C-sol
;;; type : fixnum
(defmacro AC-state-rhs-c-max (____state)  `(svref ,____state 13))

;;; solutions matrix; functional terms
;;; type : array[fixnum]
(defmacro AC-state-rhs-f-sol (____state)  `(svref ,____state 14))

;;; max value of elements of RHS-f-sol
;;; type : fixnum
(defmacro AC-state-rhs-f-max (____state)  `(svref ,____state 15))

;;; type : fixnum 11111 ... 1111
(defmacro AC-state-rhs-full-bits (____state)  `(svref ,____state 16))

;;; array of compatibility bitvectors; constants
;;; type : array[fixnum]
(defmacro AC-state-rhs-c-compat (____state)  `(svref ,____state 17))

;;; array of compatibility bitvectors; funcs
;;; type : array[fixnum]
(defmacro AC-state-rhs-f-compat (____state)  `(svref ,____state 18))

;;; number of constants on LHS after simplification
;;; type : fixnum
(defmacro AC-state-lhs-c-count (____state)  `(svref ,____state 19))

;;; number of functions on LHS after simplification
;;; type : fixnum
(defmacro AC-state-lhs-f-count (____state)  `(svref ,____state 20))

;;; number of variables on LHS after simplification
;;; type : fixnum
(defmacro AC-state-lhs-v-count (____state)  `(svref ,____state 21))

;;; number of constants on RHS after simplification
;;; type : fixnum
(defmacro AC-state-rhs-c-count (____state)  `(svref ,____state 22))

;;; number of functions on RHS after simplification
;;; type : fixnum
(defmacro AC-state-rhs-f-count (____state)  `(svref ,____state 23))

;;; t iff all solutions have been reported.
(defmacro AC-state-no-more (____state)  `(svref ,____state 24))

;;; type tag: 
;;; type : symbol
(defmacro AC-state-ac-state-p (____state)  `(svref ,____state 25))

(declaim (inline ac-state-p))
(#+GCL si::define-inline-function #-GCL defun ac-state-p (state)
  (and (vectorp state)
       (eq (svref state 25) 'ac-state)))

(defvar *half* (/ 1 2))

;; small utility.  Side effect.
(defmacro AC-Rotate-Left (_*_*_array *_*_*m)
  " shifts the element one bit to the left"
  ` (setf (svref ,_*_*_array ,*_*_*m)
          (* 2 (svref ,_*_*_array ,*_*_*m))))

(defmacro AC-note-repeats (_??mset _??array _??max _??gcd)
"; puts all repeated terms together in the list, and bashes the array
 ; (into numbers) in locations corresponding to the duplicate terms. 
 ; returns the newly grouped permutation of list.
 ; e.g. for input (a b c c c d d e f f) and #(0 0 0 0 0 0 0 0 0),
 ; this should make the array into #(0 0 3 2 1 2 1 0 2 1)."
  ` (let* ((list2 nil)
           (counter (length (the #+GCL vector #-GCL simple-vector ,_??array))))
      (declare (type fixnum counter))
      (dolist (element ,_??mset)
        (declare (type list element))
        (let ((n (cdr element)))
          (declare (type fixnum n))
          (when (> n (the fixnum ,_??max))
            (setq ,_??max n))
          (setq ,_??gcd (gcd ,_??gcd n))
          (if (> n 1) ; if it is repeated at all
              (dotimes (x n)
                (declare (type fixnum x))
                (push (first element) list2)
                (setq counter (1- counter))
                (setf (svref ,_??array counter)
                      (1+ x)))
              (progn (push (first element) list2)
                     (setq counter (1- counter))
                     ;; this line optional if 0'd array is guaranteed.
                     (setf (svref ,_??array counter) 0)))))
      list2))

#+CMU(declaim (ext:start-block match-ac-state-initialize
                               match-ac-next-state
                               match-ac-equal))

;;; x = term
;;; y = ((term . eqn-num) ... )
#||
(defun delete-one-term (x y)
  (block exit
    (if (null y)
        'none
      (if (term-is-applform? x)
          ;; application form
          (let ((head (term-head x))
                (pos nil))
            (setq pos (position-if #'(lambda (tv)
                                       (let ((term (car tv)))
                                         (and (term-is-applform? term)
                                              (method-is-of-same-operator head
                                                                          (term-head term)))))
                                   (the list y)))
              ;; (break "0")
            (unless pos
                (return-from exit :never-match))
            (if  (zerop pos)
                (if (term-equational-equal x (caar y))
                    (return-from exit (cdr y))
                  (return-from exit 'none))
              (let ((last y)
                    (rest (cdr y))
                    (cur-pos 1))
                (declare (type fixnum cur-pos))
                (loop
                  (when (= cur-pos pos)
                    (if (term-equational-equal x (caar rest))
                        (progn
                          ;; delete pattern
                          (rplacd last (cdr rest))
                          (return-from exit y))
                      (return-from exit 'none)))
                  (incf cur-pos)
                  (setq last rest rest (cdr rest))))))
        ;; term is not application form
        (if (term-equational-equal x (caar y))
            (cdr y)
          (let ((last y) (rest (cdr y)))
            (loop (when (null rest) (return 'none))
              (when (term-equational-equal x (caar rest))
                ;; delete pattern
                (rplacd last (cdr rest))
                ;; new
                (return y))
              (setq last rest  rest (cdr rest)))))))
    ))
||#

(defun delete-one-term
       (x y)
  (if (null y)
      'none
      (if (term-equational-equal x (caar y))
          (cdr y)
          (let ((last y) (rest (cdr y)))
            (loop (when (null rest) (return 'none))
                (when (term-equational-equal x (caar rest))
                  ;; delete pattern
                  (rplacd last (cdr rest))
                  ;; new
                  (return y))
              (setq last rest  rest (cdr rest))))
          ))
  )

(defvar *ac-failure-eq* nil)

(defun AC-solution-from-state (state)
  "given an AC-state, produce a solution (system of equations
 which, if true, imply the original AC equation true) from
 the matrix of 'state'"
  (let* ((ops (AC-state-operators state))
         (lhs-f (AC-state-lhs-f state))
         (lhs-v (AC-state-lhs-v state))
         (rhs-c (AC-state-rhs-c state))
         (rhs-f (AC-state-rhs-f state))
         (rhs-c-sol (AC-state-rhs-c-sol state))
         (rhs-f-sol (AC-state-rhs-f-sol state))
         (new-sys (new-m-system))
         (term-code 1)
         (rhs-subterms nil)
         (new-eqns nil))
    (declare (type fixnum term-code)
             (type #+GCL vector
                   #-GCL simple-vector
                   ops
                   lhs-f lhs-v rhs-c rhs-f rhs-c-sol rhs-f-sol)
             (type list new-sys rhs-subterms new-eqns))
    (setq *ac-failure-eq* nil)
    ;; (AC-collapse-arrays-internal lhs-v 1)
    (dotimes (i (length lhs-v))
      (declare (type fixnum i))
      (if (< i 1)
          nil
          (progn 
            (setq rhs-subterms nil)
            (setq term-code (* 2 term-code))
            ;; (AC-collapse-one-array-internal rhs-c-sol rhs-c)
            (dotimes (j (length rhs-c-sol))
              (declare (type fixnum j))
              (when (> (the fixnum (make-and (svref rhs-c-sol j)
                                             term-code))
                       0)
                (push  (car (svref rhs-c j)) rhs-subterms)))
            ;; (AC-collapse-one-array-internal rhs-f-sol rhs-f)
            (dotimes (j (length rhs-f-sol))
              (declare (type fixnum j))
              (when (> (the fixnum (make-and (svref rhs-f-sol j) term-code))
                       0)
                (push  (car (svref rhs-f j)) rhs-subterms)))
            (when rhs-subterms
              (push
               (make-equation (car (svref lhs-v i))
                              (if (cdr rhs-subterms)
                                  (make-right-assoc-normal-form-with-sort-check
                                   (svref ops (cdr (svref lhs-v i)))
                                   rhs-subterms)
                                  (first rhs-subterms)))
               new-eqns)))))
    ;;
    ;; note term-code is now the right thing. 
    ;; (AC-collapse-arrays-internal lhs-f 0)
    (dotimes (i (length lhs-f))
      (declare (type fixnum i))
      (setq rhs-subterms nil)
      (setq term-code (* 2 term-code))
      ;; (AC-collapse-one-array-internal rhs-c-sol rhs-c)
      (dotimes (j (length rhs-c-sol))
        (declare (type fixnum j))
        (when (> (the fixnum (make-and (svref rhs-c-sol j) term-code))
                 0)
          (push  (car (svref rhs-c j)) rhs-subterms)))
      ;; (AC-collapse-one-array-internal rhs-f-sol rhs-f)
      (dotimes (j (length rhs-f-sol))
        (declare (type fixnum j))
        (when (> (the fixnum (make-and (svref rhs-f-sol j) term-code))
                 0)
          (push  (car (svref rhs-f j)) rhs-subterms)))
      (when rhs-subterms
        (let ((t1 (car (svref lhs-f i)))
              (t2 (if (cdr rhs-subterms)
                      (make-right-assoc-normal-form-with-sort-check
                       (svref ops (cdr (svref lhs-f i)))
                       rhs-subterms)
                      (first rhs-subterms))))
          (let ((t1-head (term-head t1))
                (t2-head (term-head t2)))
            (if (method-is-of-same-operator+ t1-head t2-head)
                (push (make-equation t1 t2) new-eqns)
                (let ((minfo-1 (method-theory-info-for-matching
                                t1-head))
                      (minfo-2 (method-theory-info-for-matching
                                t2-head)))
                  (if (or (test-theory
                           .z. (theory-info-code minfo-1))
                          (test-theory
                           .z. (theory-info-code minfo-2)))
                      (push (make-equation t1 t2) new-eqns)
                      (progn
                        (with-match-debug ()
                          (setq *ac-failure-eq* (cons t1 t2)))
                        (setq new-eqns nil)
                        (return nil)) )))))))
    ;;
    (if new-eqns
        (progn
          (dolist (eq (nreverse new-eqns))
            (add-equation-to-m-system new-sys eq))
          (with-match-debug ()
            (format t "~%** ac-solution-from-state")
            (print-m-system new-sys))
          new-sys)
        (progn
          (with-match-debug ()
            (format t "~%** no ac solution")
            (print-next)
            (princ " - t1 = ") (term-print (car *ac-failure-eq*))
            (print-next)
            (princ " - t2 = ") (term-print (cdr *ac-failure-eq*)))
          nil))))

(#+GCL si:define-inline-function #-GCL defun test_same_term_list (x y)
  (declare (type list x y))
  (loop (when (null x) (return (null y)))
      (unless (eq (car x) (car y))
        (return nil))
    (setq x (cdr x))
    (setq y (cdr y))))

;;; SIMPLIFIED & SPECIAL PURPOSE FUNCTIONS for MULTI-SET
;;; used match-ac, match-acz.
;;; multi set is represented as a list of pairs (enty . num)
;;;  entry : element
;;;  num   : number of element in the multi set.
;;;

;;; (a b a c d a) --> ((a.3)(b.1)(d.1)(c.1))

(#+GCL si:define-inline-function #-GCL defun
       list2multi-set-list-direct (list)
  (declare (type list list))
  (let ((ms-list nil))
    (declare (type list ms-list))
    (dolist (x list)
      ;; (declare (type term x))
      (let ((ms-x (dolist (pr ms-list nil)
                    (when (term-equational-equal x (car pr))
                      (return pr))))) 
        (if ms-x 
            (incf (the fixnum (cdr ms-x))) ; (setf (cdr ms-x) (1+ (the fixnum (cdr ms-x))))
          (push (cons x 1) ms-list))))
    ms-list))

;;; Assume that t1 is NOT a variable
;;; op AC-equal: Term Term -> Bool
(defvar l2msla1 nil) (defvar l2mslv1 nil)
(defvar l2msla2 nil) (defvar l2mslv2 nil)

(defun list2multi-set-list (list)
  (declare (type list list))
  (if (and l2msla1 (test_same_term_list list l2msla1))
      (copy-alist l2mslv1)
    (if (and l2msla2 (test_same_term_list list l2msla2))
        (progn
          (rotatef l2msla1 l2msla2)
          (rotatef l2mslv1 l2mslv2)
          (copy-alist l2mslv1))
      (let ((res (list2multi-set-list-direct list)))
        (setq l2msla2 l2msla1  l2mslv2 l2mslv1)
        (setq l2msla1 list l2mslv1 res)
        (copy-alist res)))))

;;; NOTE  this is a version for AC-internal use only.
;;; it simply takes care of the "from which equation" info.
;;; the input list is like
;;; ((A . 1) (B . 2) (A . 1) (A . 3))
;;; the result is like
;;; (((A . 1) . 2) ((B . 2) . 1) ((A . 3) . 1))
;;;
(defun AC-list2multi-set (list)
  (declare (type list list))
  (let ((ms-list nil))
    (declare (type list ms-list))
    (dolist (x list) ;;(copy-tree list)
      (declare (type list x))
      (let ((ms-elt (assoc-if #'(lambda (y) 
                                  (declare (type list y))
                                  (and (= (the fixnum (cdr x))
                                          (the fixnum (cdr y)))
                                       (term-equational-equal (car y) (car x))))
                              ms-list)))
        (if ms-elt
            (progn
              (incf (the fixnum (cdr ms-elt))))
          (progn
            (push (cons x 1) ms-list)))))
    ms-list))

;;; check for multi-set equality
;;; uses term-equational-equal - which can be pretty expensive
(defun match-AC-ms-equal (x y)
  (declare (type list x y))
  (let ((lenx (length x))
        (leny (length y)))
    ;;
    (declare (type fixnum lenx leny))
    (unless (= lenx leny)
      (return-from match-ac-ms-equal nil))
    ;;
    (block the-end
      (let ((ydone 0))
        (declare (type fixnum ydone))
        (dolist (xe x)
          (declare (type list xe))
          (let ((xterm (car xe)) (xval (cdr xe)))
            (declare (type term xterm)
                     (type fixnum xval))
            (dolist (ye y (return-from the-end nil)) ; didn't find xe in y
              (declare (type list ye))
              (when (term-equational-equal xterm (car ye))
                (unless (= xval (the fixnum (cdr ye)))
                  (return-from the-end nil))
                (setq ydone (1+ ydone))
                (return)))))            ; quit the inner do-list
        (unless (= ydone leny)
          (return-from the-end nil)))
      t)))

(defun AC-next-state-sub (state)
  (do* ((m 0)                           ; only initialize these vars 
        (rhs-c-sol (AC-state-rhs-c-sol state))
        (rhs-c-max (AC-state-rhs-c-max state))
        (rhs-c-count (AC-state-rhs-c-count state))
        (rhs-c-compat (AC-state-rhs-c-compat state))
        (lhs-r-mask (AC-state-lhs-r-mask state)))
       (nil)                            ; forever
    (declare (type #+GCL vector #-GCL simple-vector rhs-c-compat) 
             (type fixnum m lhs-r-mask rhs-c-count rhs-c-max))
    (cond ((>= m rhs-c-count)           ; no next row
           (setf (AC-state-no-more state) T)
           (return))
          ((< m 0)                      ; no tests up here - could cut search here
           (let ((temp 0))              ; the empty bitvector
             (declare (type fixnum temp))
             (dotimes (s rhs-c-count)
               (declare (type fixnum s))
               (setq temp (make-or temp (svref rhs-c-sol s))))
             (setf (AC-state-LHS-mask state) temp)
             (return)))
          ((< (the fixnum (svref rhs-c-sol m)) rhs-c-max)
           (AC-Rotate-Left rhs-c-sol m)
           (when (and                   ; this is a compatible position for this bit
                  (> (the fixnum (make-and (svref rhs-c-sol m)
                                           (svref rhs-c-compat m)))
                     0)
                  ;; either this isnt a repeated term
                  (or (zerop (the fixnum
                               (make-and (svref rhs-c-sol m) lhs-r-mask)))
                      ;; or it is, and its upper neighbor is home
                      (and (< (1+ m) rhs-c-count)
                           (= (* 2 (the fixnum (svref rhs-c-sol m)))
                              (the fixnum (svref rhs-c-sol (1+ m)))))))
             (setq m (1- m))))          ; then this row is ok, else redo this row
          (t                            ; this row (m) is already maxed
           (setf (svref rhs-c-sol m) 1) ; reset this row
           (setq m (1+ m))))))

#||
(match-AC-ms-equal
 (list2multi-set-list (list-AC-subterms t1 op))
 (list2multi-set-list (list-AC-subterms t2 op)))
||#

#||
(defun match-AC-equal (t1 t2)
  (if (term-is-applform? t2)
      (let ((op (term-head t1))
            (op2 (term-head t2)))
        (declare (type method op))
        (if (method-is-of-same-operator op op2)
            (let ((sub1 (list-AC-subterms t1 op))
                  (sub2 (list-AC-subterms t2 op2)))
              (declare (type list sub1 sub2))
              (if (= (the fixnum (length sub1))
                     (the fixnum (length sub2)))
                 (dolist (s sub1 t)
                   (unless (member s sub2 :test #'term-equational-equal)
                     (return nil)))
                 nil))
            nil))
      nil))
||#

(defun match-AC-equal (t1 t2)
  (if (term-is-applform? t2)
      (let ((op (term-head t1))
            (op2 (term-head t2)))
        (declare (type method op))
        (if (method-is-of-same-operator op op2)
            (let ((sub1 (list-AC-subterms t1 op))
                  (sub2 (list-AC-subterms t2 op2)))
              (declare (type list sub1 sub2))
              (match-ac-ms-equal (list2multi-set-list sub1)
                                 (list2multi-set-list sub2)))
            nil))
      nil))

;;; ***********************
;;; ac-state-pool
;;; (defvar .ac-state-pool. nil)
;;;(defmacro allocate-ac-state ()
;;;  ` (if .ac-state-pool. (pop .ac-state-pool.)
;;;     (make-AC-state)))
;;;(defmacro deallocate-ac-state (ac-state)
;;;  `(push ,ac-state .ac-state-pool.))
;;;(eval-when (eval load)
;;;  (dotimes (x 20) (push (make-AC-state) .ac-state-pool.)))

(defun match-ac-state-initialize (sys env)
  "takes a system of equations and an environment, and 
   returns an AC-state, which is suitable for framing
   or passing to 'AC-next-state'"
  (declare (type list sys env))
  (with-match-debug ()
    (format t "~%** match-ac-state-initialize -------------------------------------")
    (print-next)
    (print-match-system-sys sys)
    (print-next)
    (print-match-system-env env))
  ;;
  (block fail
    (let ((eqn-number -1)
          (sys-operators nil)
          (all-lhs-vars nil)
          (all-lhs-funs nil)
          (all-rhs-constants nil)
          (all-rhs-funs nil)
          (*print-circle* nil))
      (declare (type (or null #-GCL simple-vector
                              #+GCL vector)
                     sys-operators)
               (type list
                     all-lhs-vars all-lhs-funs all-rhs-constants all-rhs-funs)
               (type fixnum eqn-number))
      ;;
      (dolist (equation sys)
        (incf eqn-number)
        (let* ((lhs-1 (equation-t1 equation))
               (rhs-1 (equation-t2 equation))
               (lhs-op (term-head lhs-1))
               (rhs-op (term-head rhs-1)))
          (declare (type term lhs-1 rhs-1))
          ;; quick failure cases.
          (unless (and (theory-contains-AC (method-theory lhs-op))
                       (not (term-is-builtin-constant? rhs-1))
                       (method-p rhs-op)
                       (method-is-ac-restriction-of rhs-op lhs-op))
            ;; is the first condition really need?
            ;; (format t "~&failure case #1")
            (return-from FAIL (values nil t)))
          ;;
          (let ((lhs-subs (list-AC-subterms lhs-1 lhs-op))
                (rhs-subs (list-AC-subterms rhs-1 rhs-op))
                (lhs-vars nil)
                (lhs-constants nil)
                (lhs-funs nil)
                (rhs-constants nil)
                (rhs-funs nil))
            (declare (type list lhs-subs rhs-subs lhs-vars lhs-constants
                           lhs-funs rhs-constants rhs-funs))
            ;; quick failure cases
            (when (> (the fixnum (length lhs-subs))
                     (the fixnum (length rhs-subs)))
              (return-from FAIL (values nil t))) ; no possible match
            (unless sys-operators
              (setq sys-operators (alloc-svec (the fixnum (length sys)))))
            (setf (svref sys-operators eqn-number) lhs-op)
            ;; build lhs- vars/funs/constants
            (dolist (term lhs-subs)
              (cond ((term-is-variable? term)
                     (let ((image (if env (environment-image env term) term)))
                       (cond ((null image) 
                              (push (cons term eqn-number) lhs-vars))
                             ((term-is-variable? image)
                              (push (cons image eqn-number) lhs-vars))
                             ((term-is-constant? image)
                              (push (cons image eqn-number) lhs-constants))
                             ((method-is-AC-restriction-of lhs-op
                                                           (term-head image))
                              (dolist (term2 (list-AC-subterms image
                                                               (term-head image)))
                                (cond ((term-is-variable? term2)
                                       (push (cons term2 eqn-number)
                                             lhs-vars))
                                      ((term-is-constant? term2)
                                       (push (cons term2 eqn-number)
                                             lhs-constants))
                                      (t (push (cons term2 eqn-number)
                                               lhs-funs)))))
                             (t (push (cons image eqn-number) lhs-funs)))))
                    ((term-is-constant? term)
                     (push (cons term eqn-number) lhs-constants))
                    (t (push (cons term eqn-number) lhs-funs))))
            ;; now that the lhs is partitioned - lets play with the rhs
            (dolist (term rhs-subs)
              (cond ((term-is-variable? term)
                     (push (cons term eqn-number) rhs-constants))
                    ((term-is-constant? term)
                     (let ((new (delete-one-term term lhs-constants)))
                       (if (eq 'none new)
                           (push (cons term eqn-number) rhs-constants)
                           (if (eq :never-match new)
                               (if lhs-vars
                                   (push (cons term eqn-number)
                                         rhs-constants)
                                   (progn
                                     (with-match-debug ()
                                       (format t "~%- :never-match : lhs-vars ")
                                       (print-chaos-object lhs-vars))
                                     ;; (format t "~&failure case #3")
                                     (return-from FAIL (values nil t))))
                               (setq lhs-constants new)))))
                    (t (let ((new (delete-one-term term lhs-funs)))
                         (if (eq 'none new)
                             (push (cons term eqn-number) rhs-funs)
                             (if (eq :never-match new)
                                 (if lhs-vars
                                     (push (cons term eqn-number)
                                           rhs-funs)
                                   (progn
                                     (with-match-debug ()
                                       (format t "~%- :never-match : lhs-vars ")
                                       (print-chaos-object lhs-vars))
                                     ;; (format t "~&failure case #4")
                                     (return-from FAIL (values nil t))))
                                 (setq lhs-funs new)))))))
            ;; now there are no duplicates (things appearing on both sides)
            (let ((lhs-c-count (length lhs-constants))
                  (lhs-f-count (length lhs-funs))
                  (lhs-v-count (length lhs-vars))
                  (rhs-c-count (length rhs-constants))
                  (rhs-f-count (length rhs-funs)))
              (declare (type fixnum lhs-c-count lhs-f-count lhs-v-count
                             rhs-c-count rhs-f-count))
              ;; check trivial failure conditions
              (when (or (> lhs-c-count 0) ; there ain't nothin to match it
                        (and (< lhs-v-count 1) ; no variables remain on lhs
                             (> rhs-c-count 0)) ; and constants remain on rhs
                        (> lhs-f-count rhs-f-count)) ; too many funs to match
                (return-from FAIL (values nil t))) ; FAIL most miserably
              (setq all-lhs-funs (nconc lhs-funs all-lhs-funs))
              (setq all-lhs-vars (nconc lhs-vars all-lhs-vars))
              (setq all-rhs-constants (nconc rhs-constants all-rhs-constants))
              (setq all-rhs-funs (nconc rhs-funs all-rhs-funs))))))
      ;;
      ;; done for all equations.
      ;;
      (let ((lhs-f-count (length all-lhs-funs))
            (lhs-v-count (1+ (the fixnum (length all-lhs-vars))))
                                        ; note this is "wrong"
            (rhs-c-count (length all-rhs-constants))
            (rhs-f-count (length all-rhs-funs)))
        (declare (type fixnum lhs-f-count lhs-v-count rhs-c-count rhs-f-count))
        (let ((lhs-f-r (alloc-svec-fixnum lhs-f-count))
              (lhs-v-r (alloc-svec-fixnum lhs-v-count))
              (rhs-c-r (alloc-svec-fixnum rhs-c-count))
              (rhs-f-r (alloc-svec-fixnum rhs-f-count))
              (lhs-f-ms (AC-list2multi-set all-lhs-funs))
              (lhs-v-ms (AC-list2multi-set all-lhs-vars))
              (rhs-c-ms (AC-list2multi-set all-rhs-constants))
              (rhs-f-ms (AC-list2multi-set all-rhs-funs))
              (l-m 0)
              (r-m 0))
          (declare (type #-GCL simple-vector
                         #+GCL vector
                         lhs-f-r lhs-v-r rhs-c-r rhs-f-r)
                   (type fixnum l-m r-m)
                   (type list lhs-f-ms lhs-v-ms rhs-c-ms rhs-f-ms))
          (let* ((l-gcd (or (cdar lhs-f-ms) (cdar lhs-v-ms) 1))
                 (r-gcd (or (cdar rhs-f-ms) (cdar rhs-c-ms) 1))
                 (LHS-f-list (AC-note-repeats lhs-f-ms lhs-f-r l-m l-gcd))
                 (LHS-v-list (cons (cons 'dummy 13)
                                   (AC-note-repeats lhs-v-ms lhs-v-r l-m l-gcd)))
                 (RHS-c-list (AC-note-repeats rhs-c-ms rhs-c-r r-m r-gcd))
                 (RHS-f-list (AC-note-repeats rhs-f-ms rhs-f-r r-m r-gcd)))
            (declare (type fixnum l-gcd r-gcd)
                     (type list lhs-f-list lhs-v-list rhs-c-list rhs-f-list))
            (let ((LHS-f (make-array lhs-f-count :initial-contents lhs-f-list))
                  (LHS-v (make-array lhs-v-count :initial-contents lhs-v-list))
                  (RHS-c (make-array rhs-c-count :initial-contents rhs-c-list))
                  (RHS-f (make-array rhs-f-count :initial-contents rhs-f-list))
                  (RHS-c-max (expt2 (1- lhs-v-count)))
                  (RHS-f-max (expt2 (+ -1 lhs-v-count lhs-f-count)))
                  (RHS-full-bits (- (the fixnum
                                      (expt2 (+ lhs-v-count lhs-f-count))) 2))
                  (rhs-c-sol (alloc-svec-fixnum rhs-c-count))
                  (rhs-f-sol (alloc-svec-fixnum rhs-f-count))
                  (rhs-c-compat (alloc-svec-fixnum rhs-c-count))
                  (rhs-f-compat (alloc-svec-fixnum rhs-f-count))
                  (dummy-bit 1)         ; to save a whole bunch of expt'ing
                  (lhs-r-mask 0)
                  (state (make-ac-state))
                  )
              (declare (type #-GCL simple-vector
                             #+GCL vector
                             lhs-f lhs-v rhs-c rhs-f
                             rhs-c-sol rhs-f-sol rhs-c-compat rhs-f-compat)
                       (type fixnum rhs-c-max rhs-f-max rhs-full-bits
                             dummy-bit lhs-r-mask))
              ;;
              ;; (when *match-debug*
              ;;  (format t "~%..lhs-f-ms=~s, lhs-f-r=~s lhs-v-ms=~s, lhs-v-r=~s, l-m=~d l-gcd=~d" lhs-f-ms lhs-f-r lhs-v-ms lhs-v-r l-m l-gcd)
              ;;  (format t "~&..all-rhs-funs=~s, rhs-c-ms=~s, rhs-c-r=~s, rhs-f-ms=~s, rhs-f-r=~s, r-m=~d, r-gcd=~d" all-rhs-funs rhs-c-ms rhs-c-r rhs-f-ms rhs-f-r r-m r-gcd))
              ;; one more easy failure check
              (when (or (> l-m r-m)     ; a lhs item is repeated more than any rhs
                        (not (integerp (/ r-gcd l-gcd))))
                (return-from FAIL (values nil t))) ; FAIL most miserably
              ;; NOW, get down to the real work....
              ;; setup the repeat mask (first of v's)
              (dotimes (j lhs-v-count)
                (declare (type fixnum j))
                (when (> (the fixnum (svref lhs-v-r j)) 1)
                  (setq lhs-r-mask (make-or lhs-r-mask dummy-bit))
                  (setq dummy-bit (* 2 dummy-bit))))
              ;; note dummy-bit might not be 1 here...
              (dotimes (j lhs-f-count) ; (then of f's)
                (declare (type fixnum j))
                (when (> (the fixnum (svref lhs-f-r j)) 1)
                  (setq lhs-r-mask (make-or lhs-r-mask dummy-bit))
                  (setq dummy-bit (* 2 dummy-bit))))
              ;; now setup the compatibility bitvectors (for rhs-c)
              (dotimes (i rhs-c-count)
                (declare (type fixnum i))
                (setq dummy-bit 1)
                (let ((my-repeat-count (svref rhs-c-r i)))
                  (declare (type fixnum my-repeat-count))
                  (dotimes (j lhs-v-count)
                    (declare (type fixnum j))
                    (when (and (= (the fixnum (cdr (svref rhs-c i)))
                                  (the fixnum (cdr (svref lhs-v j))))
                               ;; both are from same equation, AND
                               (or (= (the fixnum (svref lhs-v-r j))
                                      my-repeat-count)
                                   ;; the right repetition number OR 0
                                   (= (the fixnum (svref lhs-v-r j))
                                      0)))
                      (setf (svref rhs-c-compat i)
                            (make-or (the fixnum (svref rhs-c-compat i))
                                     dummy-bit)))
                    (setq dummy-bit (* 2 dummy-bit)))))
              ;; now setup the compatibility bitvectors (for rhs-f)
              (dotimes (i rhs-f-count)
                (declare (type fixnum i))
                (setq dummy-bit 1)
                (let ((my-repeat-count (svref rhs-f-r i)))
                  (declare (fixnum my-repeat-count))
                  (dotimes (j lhs-v-count)
                    (declare (type fixnum j))
                    (when (and (= (the fixnum (cdr (svref rhs-f i)))
                                  (the fixnum (cdr (svref lhs-v j))))
                               ;; both are from same equation, AND
                               (or (= (the fixnum (svref lhs-v-r j))
                                      my-repeat-count)
                                   (= (the fixnum (svref lhs-v-r j))
                                      0)))
                      (setf (svref rhs-f-compat i)
                            (make-or (the fixnum (svref rhs-f-compat i))
                                     dummy-bit)))
                    (setq dummy-bit (* 2 dummy-bit)))
                  ;; now lhs vars are taken care of, we need to deal with funs
                  (dotimes (j lhs-f-count)
                    (declare (type fixnum j))
                    ;; for now, ignore repetition of funs (can be slower)
                    (when (and (= (the fixnum (cdr (svref rhs-f i)))
                                  (the fixnum (cdr (svref lhs-f j))))
                               ;; both are from same equation, AND
                               (possibly-matches (car (svref lhs-f j))
                                                 (car (svref rhs-f i))))
                      (setf (svref rhs-f-compat i)
                            (make-or (the fixnum (svref rhs-f-compat i))
                                     dummy-bit)))
                    (setq dummy-bit (* 2 dummy-bit)))))
              ;; and now set up the initial state to a legal one
              ;; (the smallest legal one)
              ;; by just rotating the bit until it make-and's with
              ;; the compatibility vector
              (dotimes (i rhs-c-count)
                (declare (type fixnum i))
                (setq dummy-bit 1)
                (if (and (= i 0) (= rhs-f-count 0))
                    (setf (svref rhs-c-sol 0) 1)
                    (let ((my-compat (svref rhs-c-compat i)))
                      (declare (type fixnum my-compat))
                      (do ()
                          ((> dummy-bit rhs-c-max) 
                           (progn
                             ;; (format t "~&failure case #7")
                             (return-from FAIL (values nil t))))
                        (unless (zerop (make-and dummy-bit my-compat))
                          (setf (svref rhs-c-sol i) dummy-bit)
                          (return))
                        (setq dummy-bit (* 2 dummy-bit))))))
              (dotimes (i rhs-f-count)
                (declare (type fixnum i))
                (setq dummy-bit 1)
                (if (= i 0)
                    (setf (svref rhs-f-sol 0) 1)
                    (let ((my-compat (svref rhs-f-compat i)))
                      (declare (type fixnum my-compat))
                      (do ()
                          ((> dummy-bit rhs-f-max)
                           (progn ;; (deallocate-ac-state state)
                             ;; (format t "~&failure case #8")
                             (return-from FAIL (values nil t))))
                        (unless (zerop (make-and dummy-bit my-compat))
                          (setf (svref rhs-f-sol i) dummy-bit)
                          (return))
                        (setq dummy-bit (* 2 dummy-bit))))))
              ;; initialize the mask -
              (if (= rhs-f-count 0)
                  (setf (AC-state-LHS-mask state) 0)
                  (let ((temp 0))
                    (declare (type fixnum temp))
                    (dotimes (s rhs-c-count)
                      (declare (type fixnum s))
                      (setq temp (make-or temp (svref rhs-c-sol s))))
                    (setf (AC-state-LHS-mask state) temp)))
              ;; and now stuff the state full of information, and return it.
              (setf (ac-state-operators state) sys-operators
                    (ac-state-LHS-f state) lhs-f
                    (ac-state-LHS-v state) lhs-v
                    (ac-state-RHS-c state) rhs-c
                    (ac-state-RHS-f state) rhs-f
                    (ac-state-LHS-f-r state) lhs-f-r
                    (ac-state-LHS-v-r state) lhs-v-r
                    (ac-state-RHS-c-r state) rhs-c-r
                    (ac-state-RHS-f-r state) rhs-f-r
                    ;; (setf (ac-state-LHS-mask state) 0)
                    (ac-state-LHS-f-mask state) 0
                    (ac-state-LHS-r-mask state) lhs-r-mask
                    (ac-state-RHS-c-sol state) rhs-c-sol
                    (ac-state-RHS-c-max state) rhs-c-max
                    (ac-state-RHS-f-sol state) rhs-f-sol
                    (ac-state-RHS-f-max state) rhs-f-max
                    (ac-state-RHS-full-bits state) rhs-full-bits
                    (ac-state-RHS-c-compat state) rhs-c-compat
                    (ac-state-RHS-f-compat state) rhs-f-compat
                    (ac-state-LHS-c-count state) 0
                    (ac-state-LHS-f-count state) lhs-f-count
                    (ac-state-LHS-v-count state) lhs-v-count ; off 1+ intentionally
                    (ac-state-RHS-c-count state) rhs-c-count
                    (ac-state-RHS-f-count state) rhs-f-count
                    (ac-state-no-more state) nil
                    (ac-state-ac-state-p state) 'ac-state )
              ;;
              (with-match-debug () (format t "~%*** done initialization"))
              (values state nil))))))))

(defun match-AC-next-state (state)
  (declare (type #+GCL vector #-GCL simple-vector state))
  (if (not (AC-state-p state))
      (progn (format t "~% AC-Next-State given non-ac-state:~A~%" state)
             (values nil nil t))        ; failing is default behavior...
      (if (AC-state-no-more state)
          (progn
            ;; (deallocate-ac-state state)
            (values nil nil t)          ; there are no more solutions - fail
            )
          (do* ((n 0) 
                (rhs-f-sol (AC-state-rhs-f-sol state))
                (rhs-f-max (AC-state-rhs-f-max state))
                (rhs-f-compat (AC-state-rhs-f-compat state))
                (rhs-f-count (AC-state-rhs-f-count state))
                (rhs-full-bits (AC-state-rhs-full-bits state))
                (lhs-r-mask (AC-state-lhs-r-mask state)))
               (nil)                    ; forever
            (declare (type fixnum
                           n rhs-f-count rhs-f-max lhs-r-mask rhs-full-bits)
                     (type #+GCL vector #-GCL simple-vector
                           rhs-f-sol rhs-f-compat))
            (cond ((>= n rhs-f-count)   ; no next row
                   (AC-next-state-sub state)
                   (if (AC-state-no-more state)
                       (if (and (= 0 (the fixnum (ac-state-LHS-f-count state)))
                                (= 1 (the fixnum (ac-state-LHS-v-count state)))
                                (= 0 (the fixnum (ac-state-RHS-c-count state)))
                                (= 0 (the fixnum (ac-state-RHS-f-count state))))
                           (let ((sol (AC-solution-from-state state)))
                             (if sol
                                 (return (values sol state nil))
                               (if (= n 0)
                                   (return (values nil state nil))
                                 (return (values nil nil t)))))
                           (progn
                             ;; failed at f-level
                             ;; (deallocate-ac-state state)
                             (return (values nil nil t))))
                     (setq n (1- n))))
                  ((< n 0)
                   (let ((temp (AC-state-LHS-mask state)))
                     (declare (type fixnum temp))
                     (dotimes (s rhs-f-count)
                       (declare (type fixnum s))
                       (setq temp (make-or temp (svref rhs-f-sol s))))
                     (if (= rhs-full-bits temp)
                         (let ((sol (AC-solution-from-state state)))
                           (if sol
                               (return (values sol state nil))
                               (return (match-ac-next-state state))))
                         (setq n 0))))
                  ((< (the fixnum (svref rhs-f-sol n)) rhs-f-max)
                   (AC-Rotate-Left rhs-f-sol n)
                   (when (and           ; this is a compatible position for this bit
                          (> (the fixnum (make-and (svref rhs-f-sol n)
                                                   (svref rhs-f-compat n)))
                             0)
                          ;; either this isnt a repeated term
                          (or (zerop (the fixnum
                                       (make-and (svref rhs-f-sol n) lhs-r-mask)))
                              ;; or it is, and its upper neighbor is home
                              (and (< (1+ n) rhs-f-count)
                                   (= (* 2 (the fixnum (svref rhs-f-sol n)))
                                      (the fixnum (svref rhs-f-sol (1+ n)))))))
                     (setq n (1- n))))  ; then this row is ok, else redo 
                  (t                    ; this row (n) is already maxed
                   (setf (svref rhs-f-sol n) 1) ; reset this row to one
                   (setq n (1+ n))))))))

#+CMU (declaim (ext:end-block))

;; not all that useful printout of parts of AC state.
(defun AC-unparse-AC-state (AC-st)
  (format t "~%-- no more=~A~%" (AC-state-no-more AC-st))
  (format t "-- operators: ~%")
  (map nil #'print-chaos-object (AC-state-operators AC-st))
  (format t "-- RHS-f: ~%")
  (map nil #'print-chaos-object (AC-state-RHS-f AC-st))
  (format t "-- RHS-c: ~%")
  (map nil #'print-chaos-object (AC-state-RHS-c AC-st))
  (format t "-- LHS-v: ~%")
  (map nil #'print-chaos-object (AC-state-LHS-v AC-st)) 
  (format t "-- LHS-f: ~%")
  (map nil #'print-chaos-object (AC-state-LHS-f AC-st))
  (format t "-- rhs-c-count=~A, rhs-f-count=~A~%"
          (AC-state-RHS-c-count AC-st) 
          (AC-state-RHS-f-count AC-st))
  (format t "-- lhs-c-count=~A, lhs-f-count=~A, lhs-v-count=~A~%"
          (AC-state-LHS-c-count AC-st) 
          (AC-state-LHS-f-count AC-st) 
          (AC-state-LHS-v-count AC-st))
  (let ((*print-base* 2)
        (*print-array* t))              ; these be bitvectors, print them as such
    (format t "----------~%-- rhs-c-sol= ~A~&rhs-f-sol=~A~&"
            (AC-state-RHS-c-sol AC-st) (AC-state-RHS-f-sol AC-st))
    (format t "-- rhs-c-max=~A, rhs-f-max=~A, rhs-full-bits=~A~%"
            (AC-state-RHS-c-max AC-st) 
            (AC-state-RHS-f-max AC-st)
            (AC-state-RHS-full-bits AC-st))
    (format t "-- rhs-c-compat=~A, rhs-f-compat=~A~%"
            (AC-state-RHS-c-compat AC-st) 
            (AC-state-RHS-f-compat AC-st))
    (format t "-- rhs-c-r=~A, rhs-f-r=~A~%"
            (AC-state-RHS-c-r AC-st) 
            (AC-state-RHS-f-r AC-st))
    (format t "-- lhs-f-r=~A, lhs-v-r=~A~%"
            (AC-state-LHS-f-r AC-st) 
            (AC-state-LHS-v-r AC-st))
    (format t "-- lhs-mask=~A~%"
            (AC-state-LHS-mask AC-st))
    (terpri)
    (format t "-- lhs-f-mask=~A~%"
            (AC-state-LHS-f-mask AC-st))
    (format t "-- lhs-r-mask=~A~%"
            (AC-state-LHS-r-mask AC-st))))

(defun ac-args-nss (x) (AC-unparse-AC-state (car x)) (terpri))

(eval-when (:execute :compile-toplevel :load-toplevel)
  (setf (get 'AC-next-state-sub 'print-args) 'ac-args-nss))


;;; EOF
