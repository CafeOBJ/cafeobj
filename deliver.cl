;;; -*- Mode: LISP; Syntax: Common-Lisp -*-
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
(in-package :common-lisp-user)
(eval-when (eval load)
  (load "chaos-package.fasl")
  )
(defun make-app (path)
  (generate-application "CafeOBJ"
                        #-:mswindows
                        "dumps/acl-standalone/"
                        #+:mswindows
                        "dist/cafeobj-1.5/"
                        '("pignose.fasl"
                          :emacs
                          :eli
                          :sock
                          :process
                          :acldns
                          :collate
                          :euc
                          :ffcompat
                          :list2
                          :fileutil
                          :foreign
                          :trace
                          :hmac
                          :locale
                          :regexp2
                          #-:mswindows :sigio 
                          :ssl
                          :streama
                          :streamm
                          :streamc
                          :streamp)
                        :application-type :exe
                        :print-startup-message nil
                        :allow-existing-directory t
                        :copy-shared-libraries t
                        :read-init-files nil
                        :restart-app-function 'chaos::cafeobj-top-level
                        ;; :restart-init-function 'chaos::chaos-init-fun
                        :runtime :standard
                        :suppress-allegro-cl-banner t
                        :runtime-bundle t
                        :include-compiler nil
                        ;; :record-source-file-info nil
                        ;; :record-xref-info nil
                        ;; :load-source-file-info nil
                        ;; :load-xref-info nil
                        ;; :load-local-names-info nil
                        :autoload-warning t
                        :discard-local-name-info t
                        :discard-source-file-info t
                        ;; :discard-xref-into t
                        :discard-arglists t
                        :application-administration
                        '(#+:mswindows
                          (:batch-file "cafeobj.bat")
                          )
                        ))

(eval-when (eval load)
  (make-app nil))

;;; EOF
