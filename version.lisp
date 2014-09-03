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
(defvar cafeobj-version)
(defvar cafeobj-version-major)
(defvar cafeobj-version-minor)
(defvar cafeobj-version-memo)
(defvar patch-level "")

(eval-when (:execute :load-toplevel :compile-toplevel)
  (setq cafeobj-version-major "1.4")
  (setq cafeobj-version-memo (format nil "~a" "PigNose0.99"))
  (setq patch-level (format nil "~a" ""))
  (if (not (equal "" cafeobj-version-memo))
      (if (not (equal "" patch-level))
          (setq cafeobj-version-minor
	    (format nil "19b6(~a,~A)" 
		    cafeobj-version-memo
		    patch-level))
	(setq cafeobj-version-minor 
	  (format nil "19b6(~a)" cafeobj-version-memo)))
    (setq cafeobj-version-minor "19b6"))
  (setq cafeobj-version (concatenate 'string
			  cafeobj-version-major
			  cafeobj-version-minor))
  )
;; EOF
