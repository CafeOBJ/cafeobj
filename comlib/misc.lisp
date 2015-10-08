;;;-*- Mode:Lisp; Syntax:Common-Lisp; Package:CHAOS -*-
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
(in-package :CHAOS)
#|==============================================================================
                                 System: Chaos
                                 Module: comlib
                                File: misc.lisp
==============================================================================|#
#-:chaos-debug
(declaim (optimize (speed 3) (safety 0) #-GCL (debug 0)))
#+:chaos-debug
(declaim (optimize (speed 1) (safety 3) #-GCL (debug 3)))

;;;== DESCTIPTION
;;;============================================================== A
;;;collection of misc utility functions and macros.

;;; ** NOTE ********************************************************************
;;; Many of the codes in this file are cllected from articles posted to
;;; some news groups (comp.lang.lisp, comp.lang.mcl, etc) or some mailing list
;;; long ago. And some were from my personal libraries.
;;; I have no infos codes other than the codes themselves.
;;; Please let me know if you find codes which are copyrighted, or you know the
;;; author. Email: sawada@sra.co.jp.
;;; ****************************************************************************

;;; *******
;;; KEYWORD_____________________________________________________________________
;;; *******
(defvar *keyword-package* (find-package :keyword))

(defun make-keyword (name)
  (declare (type (or symbol simple-string) name)
           (values symbol))
  (if (stringp name)
      (intern name *keyword-package*)
      ;; name must be a symbol
      (intern (symbol-name name) *keyword-package*)))

;;; Searches the arglist for keyword key, and returns the following mark,
;;; or the default if supplied. If no-value is non-nil, then if nothing follows
;;; the key it is returned.

(defun extract-keyword (key arglist &optional (default nil)
                            &key (no-value nil))
  (declare (type list arglist)
           (type t default)
           (type keyword key)
           (values symbol)
           )
  (let ((binding (member key arglist :test #'eql)))
    (cond ((and (null binding) no-value)
           no-value)
          ((cdr binding)
           (cadr binding))
          (t
           default))))

;;; *****************
;;; OBJECT ALLOCATION____________________________________________________________
;;; *****************

;;; Allocating simple vector
;
#+GCL
(Clines "
static
object alloc_svec (size)
 object size;
{
  object vect ;
  vect = alloc_object(t_vector);
  vect->v.v_self = 0 ;
  vect->v.v_elttype = aet_object;
  vect->v.v_dim = Mfix(size);
  vect->v.v_displaced = Cnil ;
  vect->v.v_hasfillp = 0 ;
  vect->v.v_fillp = vect->v.v_dim;
  vect->v.v_adjustable = 0;
  array_allocself(vect, 1, Cnil);
  return vect;
}
"
)

#+GCL
(defentry alloc-svec (object) (object alloc_svec))

#-GCL
(defmacro alloc-svec (size)
  `(the simple-vector (make-array ,size :initial-element nil)))

#+GCL
(Clines "
static
object alloc_svec_fixnum (size)
 object size;
{
  object vect ;
  int i;
  vect = alloc_object(t_vector);
  vect->v.v_self = 0 ;
  vect->v.v_elttype = aet_object;
  vect->v.v_dim = Mfix(size);
  vect->v.v_displaced = Cnil ;
  vect->v.v_hasfillp = 0 ;
  vect->v.v_fillp = vect->v.v_dim;
  vect->v.v_adjustable = 0;
  array_allocself(vect, 0, small_fixnum(0));
  return vect;
}
"
)

#+GCL
(defentry alloc-svec-fixnum (object) (object alloc_svec_fixnum))

#-GCL
(defmacro alloc-svec-fixnum (size)
  ` (the simple-vector
      (make-array ,size :initial-element 0)))

;;; GCL doesn't hadle simple-vector properly!

#-(or GCL EXCL)
(defmacro %svref (vector index)
  `(svref ,vector (the fixnum ,index)))

#+EXCL
(defmacro %svref (vector index)
  `(aref (the vector ,vector) (the fixnum ,index)))

#+GCL
(defmacro %svref (vector index)
  `(aref (the vector ,vector) (the fixnum ,index)))

(declaim (inline svref aref))

;;; AT-TOP-LEVEL : -> Bool
;;; determins whether we are at top level or not.
;;; *NOTE* : the top-level must maintain the following two
;;;          variables properly:
;;;    *chaos-input-source* : buind file (or stream?) during input
;;;                           from files.
;;;    *chaos-input-level*  : buind fixnum indicating nested file
;;;                           inputs levels. 
;;;
(defun at-top-level ()
  (declare (values (or null t)))
  (and (null *chaos-input-source*)
       (<= *chaos-input-level* 0))
  )

;;; ********************
;;; ENVIRONMENT-VARIABLE________________________________________________________
;;; ********************
;;; ** TO DO for other platforms.

(defun get-environment-variable (x)
  #+(or :CCL CMU) (declare (ignore x))
  #+(or KCL GCL) (si:getenv x)
  #+LUCID (environment-variable x)
  #+CMU nil
  #+:CCL nil
  #+:Allegro (sys:getenv x)
  #+:CLISP (ext:getenv x)
  #+:SBCL (sb-ext:posix-getenv x)
  )

;;; *****
;;; DEBUG_______________________________________________________________________
;;; *****

(defvar *on-debug* nil)
(defvar *debug-level* 0)
(defmacro debug-msg ((msg &key (level 0)) &rest args)
  `(if (and *on-debug* (<= ,level *debug-level*))
       (funcall #'format *debug-io* ,msg ,@args)))
(defmacro debug-form (level &body body)
  `(if (and *on-debug* (<= ,level *debug-level*))
     (progn ,@body)))

(defun on-debug (&optional (level 1))
  (setf *on-debug* t)
  (setf *debug-level* level))

(defun off-debug ()
  (setf *on-debug* nil)
  (setf *debug-level* 0))

;;; ***************
;;; OBJECT ORDERING_____________________________________________________________
;;; ***************
;;; ordering some Common Lisp object 
;;;  symbol < cons < number < character < string < sequence
;;;   integer < symbol < cons < othernumber

(defun ob< (x y)
  (declare (type t x y))
  (eq :lt (ob-compare x y)))

(defun ob-compare (x y)
  (declare (type t x y))
  (typecase x
    (integer (typecase y
               (integer (if (< (the integer x) (the integer y))
                            :lt
                          (if (< (the integer y) (the integer x))
                              :gt
                            :eq)))
               (otherwise :lt)))
    (symbol (typecase y
              (symbol (if (eq x y)
                          :eq
                        (if (string-lessp (string (the symbol x))
                                          (string (the symbol y)))
                            :lt
                          :gt)))
              (integer :gt)
              (otherwise :lt)))
    (cons (typecase y
            (cons (let ((comp-car (ob-compare (car x ) (car y))))
                    (if (eq :eq comp-car)
                        (ob-compare (cdr x) (cdr y))
                      comp-car)))
            ((or symbol integer) :gt)
            (otherwise :lt)))
    (number (typecase y
              (number (if (< (the number x) (the number y))
                          :lt
                        (if (< (the number y) (the number x))
                            :gt
                          :eq)))
              ((or symbol integer cons) :gt)
              (otherwise :lt)))
    (character (typecase y
                 (character (if (char< (the character x)
                                       (the character y))
                                :lt
                              (if (char< (the character y)
                                         (the character x))
                                  :gt
                                :eq)))
                 ((or number cons symbol) :gt)
                 (otherwise :lt)))
    (string (typecase y
              (string (if (string-lessp (the string x) (the string y))
                          :lt
                        (if (string-lessp (the string y) (the string x))
                            :gt
                          :eq)))
              ((or character number cons symbol) :gt)
              (otherwise :lt)))
    (sequence (typecase y
                (sequence (let ((lenx (length (the sequence x)))
                                (leny (length (the sequence y))))
                            (declare (type fixnum lenx leny))
                            (dotimes (i (min lenx leny) (ob-compare lenx leny))
                              (declare (type fixnum i))
                              (let ((xi (elt x i))
                                    (yi (elt y i)))
                                (let ((cmp (ob-compare xi yi)))
                                  (unless (eq :eq cmp)
                                    (return cmp)))))
                            :eq))
                (otherwise :gt)))
    (otherwise :lt)
    ;; (structure :lt)
    ;;
    ;; how about structure ...
    ;; (otherwise (break "not yet type ~s" (type-of x)))
    ))

;;; *********
;;; TOPO-SORT___________________________________________________________________
;;; *********
;;; will only apply to sequences of distinct items
;;; very simple method based on selection sort
;;; -- select minimal element of those remaining, swap with next and continue
;;; this is specialized to lists.
;;;
(defun topo-sort (lst pred)
  (declare (type list lst)
           (type (or symbol function) pred))
  (let ((res lst))                      ; save original list as final value
  ;; run through the positions of lst successively filling them in
  (loop
    (when (null lst) (return))
    ;; pos is location of val which is current minimal value
    (let ((pos lst) (val (car lst)) (rest (cdr lst)))
      ;; scan through remainder of list rest updating pos and val
      (loop                             ; -- select minimal
        (when (null rest) (return))
        (let ((valr (car rest)))
          (when (funcall pred valr val)
            (setq pos rest val valr)))  ; have found new minimal value
        (setq rest (cdr rest)))         ; loop -- select minimal
      ;; swap values at front of lst and at pos
      (rplaca pos (car lst))
      (rplaca lst val))
    (setq lst (cdr lst)))
  res))


;;; *******
;;; ADDRESS______________________________________________________________________
;;; *******

;;; address of objects.
;;; The intention is to only use this for printing.
;;;

;;; *** TODO FOR ALLEGRO ___

#+GCL
(Clines "static object addr_of(x) object x; {return(make_fixnum((int)x));}")
;;(defCfun "object addr_of(x) object x;" 0
;;" Creturn(make_fixnum((int)x));"
;;)
#+GCL
(defentry addr-of (object) (object addr_of))

(defvar .32bit. #xffffffff)

#-GCL
(declaim (inline addr-of))

#+LUCID
(defun addr-of (x) (logand .32bit. (sys:%pointer x)))

#+CMU
(defun addr-of (x)
  (logand .32.bit. (kernel:get-lisp-obj-address x)))

#+Excl
(defun addr-of (x) (logand .32bit. (excl::pointer-to-positive-fixnum x)))

#+CCL
(defun addr-of (x) (logand .32bit. (ccl::%address-of x)))

#+CLISP
(defun addr-of (x) (logand .32bit. (sys::address-of x)))

#+SBCL
(defun addr-of (x) (logand .32bit. (sb-kernel:get-lisp-obj-address x)))

(defun print-addr (x)
  (format t "0x~8,'0x" (addr-of x)))

;;; ************
;;; QUERY-INPUT_________________________________________________________________
;;; ************
(defun query-input (&optional (default #\y) (timeout 20) 
                              format-string &rest args)
  (clear-input *query-io*)
  (when format-string
    (fresh-line *query-io*)
    (apply #'format *query-io* format-string args)
    ;; FINISH-OUTPUT needed for CMU and other places which don't handle
    ;; output streams nicely. This prevents it from continuing and
    ;; reading the query until the prompt has been printed.
    (finish-output *query-io*))
  (let ((read-char (read-char-wait timeout *query-io*)))
    (cond ((null read-char) (return-from query-input default))
          (t (unread-char read-char *query-io*)
             (read *query-io*)))))

;;; *************
;;; Y-OR-N-P-WAIT________________________________________________________________
;;; *************
;;; y-or-n-p-wait is like y-or-n-p, but will timeout
;;; after a specified number of seconds
(defun internal-real-time-in-seconds ()
  (declare (values float))
  (float (/ (get-internal-real-time) 
            internal-time-units-per-second)))

(defun read-char-wait (&optional (timeout 20) input-stream &aux char)
  (do ((start (internal-real-time-in-seconds)))
      ((or (setq char (read-char-no-hang input-stream nil)) ;(listen *query-io*)
           (< (+ start timeout) (internal-real-time-in-seconds)))
       char)))

(defvar *use-timeouts* t
  "If T, timeouts in Y-OR-N-P-WAIT are enabled. Otherwise it behaves
   like Y-OR-N-P. This is provided for users whose lisps don't handle
   read-char-no-hang properly.")

(defvar *clear-input-before-query* t
  "If T, y-or-n-p-wait will clear the input before printing the prompt
   and asking the user for input.")

;;; y-or-n-p-wait
;;;  Y-OR-N-P-WAIT prints the message, if any, and reads characters from
;;;  *QUERY-IO* until the user enters y, Y or space as an affirmative, or either
;;;  n or N as a negative answer, or the timeout occurs. It asks again if
;;;  you enter any other characters.

(defun y-or-n-p-wait (&optional (default #\y) (timeout 20) 
                                format-string &rest args)
  (when *clear-input-before-query* (clear-input *query-io*))
  (when format-string
    (fresh-line *query-io*)
    (apply #'format *query-io* format-string args)
    ;; FINISH-OUTPUT needed for CMU and other places which don't handle
    ;; output streams nicely. This prevents it from continuing and
    ;; reading the query until the prompt has been printed.
    (finish-output *query-io*))
  (loop
   (let* ((read-char (if *use-timeouts*
                         (read-char-wait timeout *query-io*)
                         (read-char *query-io*)))
          (char (or read-char default)))
     ;; We need to ignore #\newline because otherwise the bugs in 
     ;; clear-input will cause y-or-n-p-wait to print the "Type ..."
     ;; message every time... *sigh*
     ;; Anyway, we might want to use this to ignore whitespace once
     ;; clear-input is fixed.
     (unless (find char '(#\tab #\newline #\return))
       (when (null read-char) 
         (format *query-io* "~@[~A~]" default)
         (finish-output *query-io*))
       (cond ((null char) (return t))
             ((find char '(#\y #\Y #\space) :test #'char=) (return t))
             ((find char '(#\n #\N) :test #'char=) (return nil))
             (t 
              (when *clear-input-before-query* (clear-input *query-io*))
              (format *query-io* "~%Type \"y\" for yes or \"n\" for no. ")
              (when format-string
                (fresh-line *query-io*)
                (apply #'format *query-io* format-string args))
              (finish-output *query-io*)))))))

;;; ********
;;; MULTISET____________________________________________________________________
;;; ********

;;;  A multiset is a collection of elements "{e1, ..., en}" of some type, where
;;;  the elements need not be distinct. The operations "multiset.equal" is used
;;;  to determine if two elements are the same. Two elements are said to be
;;;  `distinct' in a multiset if they are not "multiset.equal" to one another.
;;;
;;;  IMPLEMENTATION:
;;;  an element is represented as a pair of the form `(object . cout)',
;;;  where, `object' is the element and `count' is the number of times it
;;;  occurs in the multiset (if it occurs at least once in the multiset).
;;;  a multiset itself is represented as a list of this pairs.

(defstruct (multiset (:conc-name "MULTISET-")
                     (:constructor multiset-create (equal-fun elements))
                     (:copier nil))
  (equal-fun #'eq :type function)       ; predicate which determines the equality
                                        ; of the objects.
  (elements nil :type list))            ; list of pair (object . count).

;;; MULTISET-NEW
;;; creates the new empty multiset-
;;;
(defmacro multiset-new (&optional (equal-fun #'eq))
  `(multiset-create ,equal-fun nil))

;;; MULTISET-IS-EMPTY m
;;;
(defmacro multiset-is-empty (m)
  `(null (multiset-elements ,m)))

;;; MULTISET-INSERT ms e
;;;  insert e in ms.
(defmacro multiset-insert (ms e)
  (once-only (ms)
    `(let* ((elems (multiset-elements ,ms))
            (pair (assoc ,e elems :test (multiset-equal-fun ,ms))))
      (if pair
          (incf (the fixnum (cdr pair)))
          (setf (multiset-elements ,ms)
                (push (cons e 1) elems))))))

;;; LIST-TO-MULTISET list
;;; returns a new multiset consisting of the elements in list.
;;;
(defmacro list-to-multiset (list &optional (equal-fun #'eq))
  ` (let ((ms (multiset-new ,equal-fun)))
      (declare (type multiset ms))
      (dolist (e ,list)
        (multiset-insert ms e))
      ms))

;;; MULTISET-TO-SET ms
;;; returns a set contains element in ms.
(defmacro multiset-to-set (ms)
  `(mapcar #'car (multiset-elements ,ms)))

;;; MULTISET-DELETE ms e
;;; removes one occurrence of e in ms.
;;;
(defmacro multiset-delete (ms e)
  (once-only (ms)
   `(let* ((elems (multiset-elements ,ms))
           (pair (assoc ,e elems :test (multiset-equal-fun ,ms))))
     (when pair
       (when (zerop (decf (the fixnum (cdr pair))))
         (setf (multiset-elements ,ms)
               (delete e elems :test (multiset-equal-fun ,ms) :key #'car)))))))

;;; MULTISET-MERGE m1 m2
;;; inserts each elements of m2 into m1. leaves m2 unchanged.
;;; equality is determined with respect to m1.
;;;
(defmacro multiset-merge (m1 m2)
  (once-only (m1)
    `(let ((m1-elems (multiset-elements ,m1))
           (equal-fun (multiset-equal-fun ,m1)))
      (dolist (e2 (multiset-elements ,m2))
        (let ((pair (assoc (car e2) m1-elems :test equal-fun)))
          (if pair
              (incf (the fixnum (cdr m1-elems)) (the fixnum (cdr pair)))
              (push e2 m1-elems)))))))

;;; MULTISET-INTERSECTION m1 m2
;;; returns a new multiset with all elements that occur in both m1 and m2,
;;; with the number of occurences being the smaller of the two.
;;; leaves m1 and m2 unchanged.
;;;
(defmacro multiset-intersectin (m1 m2)
  (once-only (m1)
     `(let ((m1-elems (multiset-elements ,m1))
            (equal-fun (multiset-equal-fun ,m1))
            (new-elems nil))
       (dolist (e2 (multiset-elements ,m2))
         (let ((pair (assoc (car e2) m1-elems :test equal-fun)))
           (when pair
             (push (cons (car pair) (min (cdr pair) (cdr e2)))
                   new-elems))))
       (multiset-create equal-fun new-elems))))

;;; MULTISET-DIFF m1 m2
;;; returns the new multiset formed by removing from m1 each elements that
;;; occurs in m2, the number of times it occurs. Thus, the relationship
;;; m1 + m2 == (m1 - m2) + (m1 ^ m2) + (m2 - m1) will hold.
;;;
(defmacro multiset-diff (m1 m2)
  (once-only (m1)
    `(let ((m1-elems (multiset-elements ,m1))
           (equal-fun (multiset-equal-fun ,m1))
           (new-elems nil))
      (dolist (e2 (multiset-elements ,m2))
        (let ((pair (assoc (car e2) m1-elems :test equal-fun)))
          (if pair
              (let ((count (- (cdr pair) (cdr e2))))
                (when (< 0 count)
                  (push (cons (car pair) count) new-elems)))
              (push (cons (car par) (cdr pair)) new-elems))))
      (multiset-create equal-fun new-elems))))

;;; MULTISET-COUNT m e
;;; returns the nubmer of occurences of e in m.
;;;
(defmacro multiset-count (m e)
  (once-only (m)
    `(let ((pair (assoc ,e (multiset-elements ,m) :test (multiset-equal-fun ,m))))
      (if pair
          (cdr pair)
          0))))

;;; MULTISET-COPY m
;;; returns a new multiset with the same contents and the same equality function as m.
;;;
(defmacro multiset-copy (m)
  `(multiset-create (multiset-equal-fun ,m)
                    (copy-tree (multiset-elements ,m))))

;;; ***********
;;; Boolean Ops_________________________________________________________________
;;; ***********

;;; define boolean control extensions to and, or, not... the bit operators
;;; are there, but not the more general short-circuting ones. 
;;; Some of these will only make sense on two operands, and many can't short
;;; circuit (exclusive ops, for instance).

;;; xor
;;;   True only if exactly one predicate is true. Short circutes when it finds
;;;   a second one is true. Returns the true predicate.

#-:Allegro-v6.0
(defmacro xor (&rest predicates)
  (let ((result (gensym))
        (temp (gensym))
        (block-name (gensym)))
    `(block ,block-name
       (let ((,result ,(car predicates))
             ,temp)
         ,@(let (code-result)
             (dolist (pred (cdr predicates))
               (push `(cond
                        ((and (setq ,temp ,pred)
                              ,result)
                         (return-from ,block-name nil))
                        (,temp
                         (setq ,result ,temp)))
                     code-result))
             (nreverse code-result))
         ,result))))
         
;;; nand
;;;   True only if all predicates are not true. Short circutes when it finds
;;;   one is false.

(defmacro nand (&rest predicates)
  (let ((block-name (gensym)))
    `(block ,block-name
       ,@(let (code-result)
           (dolist (pred predicates)
             (push `(if (not ,pred)
                        (return-from ,block-name t))
                   code-result))
           (nreverse code-result))
       nil)))

;;; nor
;;;  True only if all predicates are false. Short circutes when it finds a one
;;;  is true.

(defmacro nor (&rest predicates)
  (let ((block-name (gensym)))
    `(block ,block-name
       ,@(let (code-result)
           (dolist (pred predicates)
             (push `(if ,pred
                        (return-from ,block-name nil))
                   code-result))
           (nreverse code-result))
       t)))


;;; ****
;;; TIME________________________________________________________________________
;;; ****

(defun get-time-string (&optional universal-time)
  (unless universal-time (setf universal-time (get-universal-time)))
  (multiple-value-bind (secs min hour date month year dow)
      (decode-universal-time universal-time 0) ; GMT time
    (declare (type fixnum dow month))
    (format nil "~d ~a ~d ~a ~d:~2,'0d:~2,'0d GMT"
            year
            (%svref '#(0 "Jan" "Feb" "Mar" "Apr" "May"
                        "Jun" "Jul" "Aug" "Sep" "Oct"
                        "Nov" "Dec")
                    month)
            date
            (%svref '#("Mon" "Tue" "Wed" "Thu" "Fri" "Sat" "Sun") dow)
            hour min secs)
    ))

;;; elapsed-time-in-seconds
;;;
;;;  Returns the time in seconds that has elapsed between Base and Now.
;;;  Just subtracts Base from Now to get elapsed time in internal time units,
;;;  then divides by the number of internal units per second to get seconds.

(defun elapsed-time-in-seconds (base now)
  (declare (type integer base now)
           (values single-float))
  (coerce (/ (- now base)
             internal-time-units-per-second)
          'single-float))

(defun time-in-seconds (sum)
  (declare (type integer sum)
           (values single-float))
  (coerce (/ sum internal-time-units-per-second) 'single-float))

;;; ****
;;; MISC________________________________________________________________________
;;; ****

(defmacro every2len (fn l1 l2)
  (let* ((lmbd (cadr fn))
         (args (cadr lmbd))
         (bdy (cddr lmbd)))
    ` (let ((lst1 ,l1) (lst2 ,l2) ,@args)
        (loop
         (when (null lst1) (return (null lst2)))
         (when (null lst2) (return (null lst1)))
         (setq ,(car args) (car lst1))
         (setq ,(cadr args) (car lst2))
         (unless (progn ,@bdy) (return nil))
         (setq lst1 (cdr lst1))
         (setq lst2 (cdr lst2))
         )
        )))

(defun list2array (list)
  (declare (type list list)
           #-GCL (values simple-vector)
           )
  #-GCL
  (make-array (length list) :initial-contents list)
  #+GCL
  (let ((len (length list)))
    (let ((arr (si:make-vector t len nil nil nil 0 nil)) (i 0))
      (declare (fixnum i))
      (dolist (e list) (si:aset arr i e) (setq i (1+ i)))
      arr)))

(defun make-list-1-n (n)
  (declare (type fixnum n)
           (values list))
  (let ((result nil))
    (dotimes-fixnum (x n)
      (push (+ x 1) result))
    (reverse result)))

(defun make-list-1-n-0 (n)
  (declare (type fixnum n)
           (values list))
  (let ((result nil))
    (dotimes-fixnum (x n)
      (push (+ x 1) result))
    (push 0 result)
    (reverse result)))

;;;
;;; REMOVEABLE ASSOCIATION TABLE 
;;;
(defmacro find-in-assoc-table (table key &optional (test '#'equal))
  `(cdr (assoc ,key ,table :test ,test)))

(defmacro get-entry-in-assoc-table (table key &optional (test '#'equal))
  `(assoc ,key ,table :test ,test))

(defmacro delete-entry-from-assoc-table (table key &optional (test '#'equal))
  ` (let ((entry (assoc ,key ,table :test ,test)))
      (when entry
        (setq ,table (delete entry ,table :test #'eq)))))

(defmacro delete-object-from-assoc-table (table object &optional (test '#'eq))
  ` (let ((entry (rassoc ,object ,table :test ,test)))
      (when entry
        (setq ,table (delete entry ,table :test #'eq)))))

(defmacro add-to-assoc-table (table key value &optional (test '#'equal))
  (once-only (table key value)
    ` (let ((entry (get-entry-in-assoc-table ,table ,key ,test)))
        (if entry
            (setf (cdr entry) ,value)
            (prog1
                ,value
              (push (cons ,key ,value) ,table))))))

(defmacro object-is-in-assoc-table? (table object &optional (test '#'eq))
  `(rassoc ,object ,table :test ,test))

;;; *******************
;;; FIXNUM COMPUTATIONS
;;; *******************


;; (declaim (inline test-and make-and make-or make-xor))
;; (declaim (inline logand logior logxor))
;; #-GCL (declaim (ftype (function (fixnum fixnum) (or null t)) test-and))
;; #-GCL (declaim (ftype (function (fixnum fixnum) (or null t)) make-and))
;; #-GCL (declaim (ftype (function (fixnum fixnum) (or null t)) make-or))
;; #-GCL (declaim (ftype (function (fixnum fixnum) (or null t)) make-xor))

#+gcl (Clines "static object test_and (a, b) object a, b;
        {register int x = fix(a); register int y = fix(b); return(x & y) ? Ct : Cnil;}")
#+gcl (defentry test-and (object object) (object test_and))
#-gcl
(defmacro test-and (a b)
  `(not (zerop (logand (the fixnum ,a) (the fixnum ,b)))))

#+gcl (Clines "static object make_and (a, b) object a, b;
        {register object res = alloc_object(t_fixnum);
         register int x = fix(a); register int y = fix(b);
         fix(res) = x & y;
         return res;}")
#+gcl (defentry make-and (object object) (object make_and))
#-gcl
(defmacro make-and (*a *b)
  `(logand (the fixnum ,*a) (the fixnum ,*b)))

#+gcl (Clines "static object make_or (a,b) object a,b;
         {register object x = alloc_object(t_fixnum);
          register int ax = fix(a); register bx = fix(b);
          fix(x) = ax | bx;
          return x;}")
#+gcl (defentry make-or (object object) (object make_or))
#-gcl
(defmacro make-or (*a *b)
  `(logior (the fixnum ,*a) (the fixnum ,*b)))

#+gcl (Clines "static object make_xor (a,b) object a,b;
        {register object x = alloc_object(t_fixnum);
        register int ax = fix(a); register bx = fix(b);
        fix(x) = ax ^ bx;
        return x;}")
#+gcl (defentry make-xor (object object) (object make_xor))
#-gcl
(defmacro make-xor (*a *b)
  `(logxor (the fixnum ,*a) (the fixnum ,*b)))

#+gcl (Clines "static object expt_fixnum (a, b) object a,b;
        {object result = alloc_object(t_fixnum);
         unsigned int x = fix(a);
         unsigned int y = fix(b);
         unsigned int z = 1;
         while (y > 0)
           if (y%2 == 0) { x *= x; y /= 2; } else {z *= x; --y;}
         fix(result) = z;
         return result;}")

#+gcl (defentry expt-fixnum (object object) (object expt_fixnum))

;;; (declaim (inline expt-fixnum expt2))
#-gcl
(defmacro expt-fixnum (x y)
  `(expt (the fixnum ,x) (the fixnum ,y)))

#+gcl
(Clines "
  static unsigned int bit_vector[32] = {
     1<<0, 1<<1, 1<<2, 1<<3, 1<<4, 1<<5, 1<<6, 1<<7, 1<<8, 1<<9,
     1<<10, 1<<11, 1<<12, 1<<13, 1<<14, 1<<15, 1<<16, 1<<17, 1<<18, 1<<19,
     1<<20, 1<<21, 1<<22, 1<<23, 1<<24, 1<<25, 1<<26, 1<<27, 1<<28, 1<<29,
     1<<30, 1<<31,
 };"
        )

#+gcl
(Clines "static object expt2 (a) object a;
       {unsigned int res;
        register int x = fix(a);
        if (x < 32) {
           return (make_fixnum(bit_vector[x]));
        } else { FEerror(\"aho\");}
       }"
        )

#+gcl
(defentry expt2 (object)(object expt2))

;;; (declaim (inline expt2))
#-gcl
(defmacro expt2 (x)
  `(expt 2 (the fixnum ,x)))

;;; EOF
