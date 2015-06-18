;;;-*- Mode:LISP; Package: Chaos; Base:10; Syntax:Common-lisp -*-
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
                                 System: Chaos
                               Module: primitives
                               File: depend.lisp
==============================================================================|#
#-:chaos-debug
(declaim (optimize (speed 3) (safety 0) #-GCL (debug 0)))
#+:chaos-debug
(declaim (optimize (speed 1) (safety 3) #-GCL (debug 3)))

;;; ****************************************************************************
;;; ************************* MODULE DEPENDENCY GRAPH **************************
;;; ****************************************************************************

(defvar *contradictions* nil)
;;; (defvar *module-dep-debug* nil)

;;; DEPENDENCY LINK

;;; DDLINK
;;; a labeled link to a ddnode.
;;; ddlink     = < label, ddnode >
;;; label      = T | NIL
;;; mode       = { :protecting | :extending | :using }
;;; ddnode     = a ddnode
;;;
(defstruct (ddlink (:print-function (lambda (ddl stream depth)
                                      (declare (ignore depth))
                                      (format stream "< ~s : ~s <- ~s >"
                                              (ddlink-label ddl)
                                              (ddlink-mode ddl)
                                              (ddlink-ddnode ddl)))))
  (label nil :type (or null t))
  (mode nil :type symbol)
  (ddnode nil :type ddnode)
  )

;;; DDCLAUSE
;;; list of ddlinks
;;; ddclause = < id, List[link] >
;;; id       = symbol (one of :protecting, :extending, :using).
;;; ddlinks  = a list of ddlinks
;;;
(defstruct (ddclause (:print-function (lambda (ddc stream depth)
                                        (declare (ignore depth))
                                        (format stream "~s" (ddclause-id ddc)))))
  (id nil :type symbol)
  (ddlinks nil :type list)
  )

;;; DDNODE
;;; ddnode    = < id, label, List[ddclause] >
;;; id        = module
;;; label     = current label (T, NIL, or default 'out)
;;; ddclauses = list of the ddclauses pointing to this node.
;;;
(defstruct (ddnode (:print-function (lambda (ddn stream depth)
                                      (declare (ignore depth))
                                      (format stream "( ~s: ~s)"
                                              (ddnode-id ddn)
                                              (ddnode-label ddn)))))
  (id nil :type top-object)
  (label 'out :type symbol)
  (ddclauses nil :type list)
  )

(defun new-module-node (mod)
  (declare (type top-object mod)
           (values ddnode))
  (make-ddnode :id mod))

(defun get-ddlink (label ddn)
  (declare (type symbol label)
           (type ddnode ddn)
           (values ddlink))
  (make-ddlink :label label :ddnode ddn))

#||
        < id, ( ddlink-1, ... , ddlink-n ) >               ** DDCLAUSE
                            /
                           /
        < label, mode, ddnode >                            ** DDLINK
                        /
                       /
        < module, label, (ddclause-1, ... , ddclause-n ) > ** DDNODE

||#

;;; LABEL-DDNODE
;;;
(defun label-ddnode (ddn new-label)
  (declare (type ddnode ddn)
           (type symbol new-abel)
           (values t))
  (let ((old-label (ddnode-label ddn)))
    (cond ((not (eq old-label new-label))
           (show-ddnode-change ddn
                               old-label
                               new-label)
           (setf (ddnode-label ddn) new-label)))))

;;; ATTACH-DDCLAUSE : ddclause -> 'void
;;; make all the ddnodes in ddclause point back to ddcualse.
;;;
(defun attach-ddclause (ddc)
  (dolist (ddl (ddclause-ddlinks ddc))
    (pushnew ddc (ddnode-ddclauses (ddlink-ddnode ddl)))))

;;; DETACH-DDCLAUSE
;;; undo attach-ddclause
;;;
(defun detach-ddclause (ddc)
  (dolist (ddl (ddclause-ddlinks ddc))
    (setf (ddnode-ddclauses (ddlink-ddnode ddl))
          (delete ddc (ddnode-ddclauses (ddlink-ddnode ddl))))))

;;; CONTRADICT
;;; enter contradicting ddclause into *contradictions*
;;;
(defun contradict (ddc)
  (push ddc *contradictions*))

;;; UNCONTRADICT
;;; remove ddclause from *contradictions*
;;;
(defun uncontradict (ddc)
  (if (member ddc *contradictions* :test #'eq)
      (remove ddc *contradictions*)))

;;; PRUNE-CONTRADICTIONS
;;; remove all ddclauses that are no longer contradicted from the list of contradictions.
;;;
(defun prune-contradictions ()
  (setq *contradictions*
        (delete-if-not #'contradicted-p *contradictions*)))

(defun init-module-depg (&optional debug-flag)
  (setq *contradictions* nil)
  (setq *module-dep-debug* debug-flag))

;;; PREMISE-P : ddclause -> Bool
;;; true iff ddclause has only one link
;;;
(defun premise-p (ddc)
  (and (ddclause-ddlinks ddc)
       (null (cdr (ddclause-ddlinks ddc)))))

;;; DDNODE-IN-P : ddnode -> Bool
;;; true iff ddnode is labeled T or NIL
;;;
(defun ddnode-in-p (ddn)
  (memq (ddnode-label ddn) '(t nil)))

;;; DDNODE-OUT-P : ddnode -> Bool
;;; true iff ddnode is labeled 'out
;;;
(defun ddnode-out-p (ddn)
  (eq (ddnode-label ddn) 'out))

;;; DDLINK-MISALIGEND-P : ddlink -> Bool
;;; true iff ddlink is misaligned.
;;;
(defun ddlink-misaligned-p (ddl)
  (eq (not (ddlink-label ddl))
      (ddnode-label (ddlink-ddnode-ddl))))

;;; CONTRADICTED-P : ddclause -> Bool
;;; true iff ddclause is contradicted.
;;;
(defun contradicted-p (ddc)
  (every #'ddlink-misaligned-p
         (ddclause-ddlinks ddc)))

;;; MISALIGNED-DDLINKS : ddclause if-all if-all-but-one -> {   NIL
;;;                                                          | value returned by if-all or
;;;                                                            if-all-but-one }
;;; If all the ddlinks in ddclause are misaligned, pass ddclause to if-all.
;;; If all but one ddlink is misaligned, pass ddclause and the misaligned
;;;    ddlink to if-all-but-onde.
;;; If more than one ddlink is not misaligned, return NIL.
;;;
(defun misaligned-ddlinks (ddc if-all if-all-but-noe)
  (let ((non-misaligned-links (remove-if $'ddlink-misaligned-p
                                         (ddclause-ddlinks ddc))))
    (cond ((null non-misaligned-links)
           (funcall if-all ddc))
          ((null (cdr non-misaligend-links))
           (funcall if-all-but-one ddc
                    (car non-misaligned-links)))
          (t nil))))

(defun return-t (x &optional y)
  (declare (ignore x y))
  t)

(defun return-nil (x &optional y)
  (declare (ignore x y))
  nil)

;;; DDCCLAUSE-ACTIVE-DDNODE : ddclause -> Nil or ddnode
;;; get the active node for ddclause, if any.
;;;
(defun ddclause-active-ddnode (ddc)
  (misaligned-ddlinks ddc
                      #'return-nil
                      #'(lambda (ddc dl) (declare (ignore ddc))
                                (ddlink-ddnode ddl))))

;;; ASSERT-PREMISE ddclause-id label ddnode -> ddclause
;;; assert that ddnode has the given label.
;;;
(defun assert-premise (id label ddn)
  (assert-ddlinks id (list (get-ddlink label ddn))))

;;; ASSERT-AT-LEAST-ONE : ddclause-id ddnode-list -> ddclause
;;; assert that at least one ddnode is true.
;;;
(defun assert-at-least-one (id ddnodes)
  (assert-ddlinks id (mapcan #'(lambda (ddn) (list (get-ddlinks t ddn)))
                             ddnodes)))

;;; ASSERT-AT-MOST-ONE : ddclause-id ddnode-list -> ddclause
;;; assert that at most one ddnode is true, i.e., at least one of
;;; every pair is false.
;;;
(defun assert-at-most-one (id ddnodes)
  (mapc #'(lambda (ddn1)
            (mapc #'(lambda (ddn2)
                      (assert-ddlinks id
                                      (list (get-ddlink nil ddn1)
                                            (get-ddlink nil ddn2))))
                  (cdr (member ddn1 ddnodes))))
        ddnodes))

;;; ASSERT-DDLINKS : ddclause-id ddlink-list -> ddclause
;;; make a clause of the links and assert it.
;;;
(defun assert-ddlinks (id ddlinks)
  (assert-ddclause (make-ddclause :id id :ddlinks ddlinks)))

;;; ASSERT-DDCLAUSE : ddclause -> ddclause
;;; attach ddclause and label.
;;;
(defun assert-ddclause (ddc)
  (show-ddnetwork-change "Asserting " ddc)
  (attach-ddclause ddc)
  (propagate-labels ddc)
  ddc)

;;; RETRACT-DDCLAUSE : ddclause -> void
;;; detach clause from the network and delabel.
;;;
(defun retract-ddclause (ddc)
  (show-ddnetwork-change "Retracting " ddc)
  (detach-ddclause ddc)
  (propagate-out-labels ddc))

;;;  FOR DEBUG 
(defun show-ddnode-change (ddn old-label new-label)
  (if *module-dep-debug*
      (format t "~%~s ~s -> ~s"
              (ddnode-id ddn) old-label new-label)))

(defun show-ddnetwork-change (message ddc)
  (if *module-dep-debug*
      (let ((ddlinks (ddclause-ddlinks ddc)))
        (format t "~%~a" message)
        (cond (ddlinks
               (show-ddlink (car ddlinks))
               (mapc #'(lambda (ddl)
                         (princ " or ")
                         (show-ddlink ddl))
                     (cdr ddlinks)))))))

(defun show-ddlink (ddl)
  (format t "~s~s"
          (case (ddlink-label ddl)
            ((t) '+)
            ((nil) '-)
            (otherwise '?))
          (ddnode-id (ddlink-ddnode ddl))))

(defun show-contracitions ()
  (cond (*contracictions*
         (format t "~% Thre are contradictions.~%~S" *contradictions*)
         (mapc #'(lambda (ddc)
                   (format t "~%~S caused by ~S~%" ddc (contradiction-causes ddc)))
               *contradictions*))))

;;; PROPAGATE-LABELS : ddclause -> void
;;; propagate T and NIL labels to ddclauses's ddnode.
;;; 
(defun propagate-labels (ddc)
  (misaligend-ddlinks ddc
                      #'contradict
                      #'align-ddlink))

;;; ALIGN-DDLINK ddclause ddlink -> void
;;; mark the label of ddlink's ddnode agree with ddlink's label,
;;; and propagatge labels to the other ddclauses pointing to that ddnode.
;;;
(defun align-ddlink (ddc1 ddl)
  (let ((ddn (ddlink-ddnode ddl)))
    (cond ((ddnode-in-p ddn) nil)
          (t (label-ddnode ddn (ddlink-label ddl))
             (dolist (ddc2 (ddnode-ddclauses ddn))
               (unless (eq ddc1 ddc2)
                 (propagate-labels ddc2)))))))

;;; PROPAGATE-OUT-LABLES : ddclause -> void
;;; mark 'OUT those ddnodes that may have been forced to a label by ddclause.
;;; (ddclase is being retracted.)  prune contradictions.
;;; call PROPAGATE-LABELS with clauses needing relabeling.
;;;
(defun propagate-out-labels (ddc)
  (misaligned-ddlinks ddc
                      #'uncontradict
                      #'(lambda (ddc1 ddl)
                          (dolist (ddc2 (delabel-ddnode (ddlink-ddnode ddl)))
                            (propagate-labels ddc2))
                          (prune-contradictions))))

;;; DELABEL-DDNODE : ddnode -> List[ddclause]
;;; delabel all ddnodes that were justfied by this ddnode, and return all ddclauses
;;; that might relabel ddnode.
;;; *NOTE* get the justificands BEFORE delabeling ddnode, and the justifications
;;;        AFTER the recursive delabeling.
;;;
(defun delabel-ddnode (ddn)
  (cond ((ddnode-out-p ddn) nil)
        (t (let ((going-out (ddnode-jistificands ddn)))
             (label-ddnode ddn 'out)
             (nconc (mapcan #'(lambda (ddn)
                                (delabel-ddnode ddn))
                            going-out)
                    (ddnode-justifications ddn))))))

;;; DDNODE-JISTIFICATIONS : ddnode -> List[ddclause]
;;; return the ddclauses that five ddnode its label.
;;;
(defun ddnode-justifications (ddn)
  (mapcan #'(lambda (ddc)
              (if (eq (ddclause-active-ddnode ddc) ddc)
                  (list ddc)
                  nil))
          (ddnode-ddclauses ddn)))

;;; DDNODE-JUSTIFICANTS : ddnode -> List[ddnode]
;;; return the ddnodes that were propagated by labels from ddnode.
;;;
(defun ddnode-justificants (ddn1)
  (remove-if-not #'(lambda (ddc)
                     (let ((ddn2 (ddclause-active-ddnode ddc)))
                       (and (not (eq ddn1 ddn2)) ddn2)))
                 (ddnode-ddclauses ddn1)))

;;; EOF
