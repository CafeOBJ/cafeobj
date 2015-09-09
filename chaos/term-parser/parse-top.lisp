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
#|==============================================================================
                                  System:Chaos
                            Module:term-parser.chaos
                            File: parse-engine.lisp
==============================================================================|#
#-:chaos-debug
(declaim (optimize (speed 3) (safety 0) #-GCL (debug 0)))
#+:chaos-debug
(declaim (optimize (speed 1) (safety 3) #-GCL (debug 3)))

;;;                     SIMPLE PARSER TOP LEVEL ROUTINES

(defun simple-parse-from-string (string &optional
                                        (module *current-module*)
                                        (sort *cosmos*))
  (declare ;; (type simple-string string)
           (type module module)
           (type sort* sort))
  (with-in-module (module)
    (setf string (read-term-from-string string))
    ;; (prepare-for-parsing module)
    (let ((*parse-variables* nil))
      (simple-parse module string sort))))

(defun simple-parse-from-string* (string &optional
                                         (module *current-module*)
                                         (sort *cosmos*))
  ;; (prepare-for-parsing module)
  (simple-parse module string sort))

(defvar *parse-raw-parse* 'none)

(defvar .saved-ambiguous. nil)

;;; SIMPLE-PARSE : module list-of-tokens &optional sort-constraint -> term
;;;
(defun simple-parse (module preterm &optional (sort *cosmos*))
  (declare (type module module)
           (type (or string list) preterm)
           (type sort* sort))
  (with-in-module (module)
    (when (stringp preterm)
      (setf preterm (read-term-from-string preterm)))
    (if (null preterm)
        (progn
          (with-output-simple-msg ()
            (princ "[Error] empty input, no parse."))
          (make-bconst-term *syntax-err-sort* '(the input is empty)))
      (let ((res nil))
        (setq res (catch :parse-error
                    (parse-term preterm module parser-max-precedence sort)))
        (when *on-parse-debug*
          (format t "~%[simple-parse] preterm= ~s, parsed term = " preterm)
          (print-terletox-list res))
        (let* ((final-well-defined (mapcan #'(lambda (e)
                                               ;; e ::= ((term . prec) . remaning-tokens)
                                               (when (and (null (cdr e)) ; no remaining tokens
                                                          (not (term-ill-defined
                                                                (caar e))))
                                                 (list (caar e))))
                                           res))
               (final (if final-well-defined
                          final-well-defined
                        (mapcan #'(lambda (e)
                                    ;; gather ones without remaining tokens
                                    (unless (cdr e)
                                      (list (caar e))))
                                res)))
               (partial (if final
                            nil
                          (let ((len 0)
                                ;; gather partially parsed ones
                                (val nil))
                            (dolist (e res val)
                              (if (< len (length (the list (cdr e))))
                                  (setf val (cons (caar e) (cdr e))))))))
               (result nil))
          ;;
          (cond (partial (setf result
                           ;; syntax error: partially parsed
                               (make-applform *syntax-err-sort*
                                              *partial-method*
                                              (list (car partial)
                                                    (make-bconst-term *universal-sort*
                                                                      (cdr partial))))))
                (final (if (term-ill-defined (car final))
                           (setf result (car final))
                         (setf result 
                           (if (null (cdr final))
                               (car final)
                             (select-parse module final t)))))
                (t (setf result (make-bconst-term *syntax-err-sort*
                                                  ;; whole term could not be parsed
                                                  (if res
                                                      res
                                                      preterm)))))
          ;;
          (setq *parse-raw-parse* result)
          (when (term-ill-defined result)
            (with-output-simple-msg ()
              (format t "~&[Error] no successful parse")))
          (parse-convert result module))))))

(defun select-parse (module final &optional print-warning)
  (declare (type module module)
           (type list final)
           (type t print-warning))
  (let ((*print-with-sort* t)
        (*fancy-print* nil))
    (setq .saved-ambiguous. final)
    ;; minimize the ambiguity.
    (setq final (pre-choose-final module final))
    (unless (cdr final)
      (return-from select-parse (car final)))
    ;;
    (when print-warning
      (with-output-chaos-warning ()
        (princ "Ambiguous term:")
        (print-next)
        (princ "please try `check regularity' command.")
        (print-next)
        (princ "if the signature is regular, there possibly be ")
        (print-next)
        (princ "some name conflicts between operators and variables.")))
    ;;
    (print-next)
    (if *select-ambig-term*
        (progn
          (princ "* Please select a term from the followings:")
          (print-next)
          (parse-show-diff final)
          (print-next)
          ;; select a term
          (let ((choise 1)
                user-choise
                (num (length final)))
            (declare (type fixnum choise num))
            ;; query user
            (setq user-choise
              (query-input
               1
               60
               "* Please input your choice (a number from 1 to ~d, default is 1)? "
               num))
            (cond ((and (numberp user-choise) (<= (the fixnum user-choise) num))
                   (setf choise user-choise)
                   (format t "Taking the ~:R as correct.~%" choise))
                  (t (format t "Arbitrarily taking the ~:R as correct.~%" choise)))
            (nth (1- choise) final)))
      (progn
        (parse-show-diff final)
        (make-bconst-term *syntax-err-sort* "ambiguous term")))))
  
(defun pre-choose-final-sub (module final)
  (declare (type module module)
           (type list final))
  ;; here we minimize the set of candidates of possible result of parsing.
  (let ((well )
        (min nil)
        (so (module-sort-order module))
        (res nil))
    (declare (type list well res min)
             (type sort-order so))
    ;; of course, ill sorted terms detected during parsing procs. are
    ;; out of our focus. 
    ;; miserablly terminates when all are ill-defined terms...
    (setq well (remove-if #'(lambda (x)
                             (not (term-is-really-well-defined x)))
                          final)) 
    (unless well (return-from pre-choose-final-sub final))

    ;; select the lowest parses among possibilities.
    ;; this might be redundant because we has been trying to get the
    ;; lowest operator so far.
    ;; 2010/7/3: we must not eliminate variables!!!!!!!!
    ;;
    (setf min (minimal-sorts (mapcar #'(lambda (x) (term-sort x)) well)
                             so))
    (dolist (f well)                    ; filter out terms with
                                        ; non-minimal sort. 
      (when (or (term-is-variable? f)
                (memq (term-sort f) min))
        (push f res)))

    ;; special case for terms of *universal-sort*, they may have some
    ;;; ill-formed terms in their subterms.

    (if (or (sort= (car min) *cosmos*)
            (sort= (car min) *universal-sort*)
            (sort= (car min) *huniversal-sort*))
        (let ((pres (remove-if #'(lambda (x)
                                   (and (term-is-application-form? x)
                                        (some #'term-contains-error-method
                                              (term-subterms x))))
                               res)))
          (if pres
              ;; if there are some remaining terms serviving these
              ;; hard checks, they can be the result.
              pres
            ;; OK, we failed in a test. let ask users which we should 
            ;; take as a result.
            res))
      res)))

(defun pre-choose-final (module final)
  (declare (type module module)
           (type list final))
  ;; due to our parsing algorithm (no flames are welcom), possibly
  ;; the same (in a sense of term-is-similar?) terms can co-exist.
  (setq final (delete-duplicates final :test #'term-is-similar?))
  (let ((result final))
    (when (and (cdr final) (assoc *id-module* (module-all-submodules module)))
      (setq result (remove-if #'(lambda (x) (sort= *id-sort* (term-sort x))) final)))
    (when (every #'(lambda(x) (term-is-application-form? x)) result)
      (when *on-operator-debug*
        (format t "~%[pre-choose-final]")
        (dolist (tx final)
          (terpri)
          (print-chaos-object (term-head tx))
          (princ ": ")
          (term-print-with-sort tx)))
      (let ((mslist (mapcar #'(lambda (x) (term-head x)) result))
            (least-op nil)
            (gen-op nil)
            (res nil))
        (with-in-module (module)
          (cond ((null (cdr mslist))
                 ;; do nothing
                 )
                ((null (cdr (remove-duplicates mslist :test #'(lambda (x y) (method= x y)))))
                 ;; check subterms and select one
                 (setq result (choose-most-apropreate-term result)))
                (t ;; first find the lowest one
                 (setq least-op (choose-lowest-op mslist))
                 (cond (least-op
                        (if (method= *bool-if* least-op)
                            (setq res (select-if-then-least result (module-sort-order module)))
                          (push (find-if #'(lambda (x) (method= least-op (term-head x)))
                                         result)
                                res))
                        (setq result res))
                       (t (setq gen-op (choose-most-general-op mslist))
                          ;; then select most general one
                          (when gen-op
                            (push (find-if #'(lambda (x) (method= gen-op (term-head x))) result)
                                  res)
                            (setq result res)))))))))
    (if result
        (pre-choose-final-sub module result)
      (pre-choose-final-sub module final))))

;;; select a one among terms with the same top operator 
(defun choose-most-apropreate-term (terms)
  (unless (term-subterms (car terms))
    ;; this is very strange case
    (return-from choose-most-apropreate-term nil))
  (let ((res nil))
    (dolist (term terms)
      (when (every #'(lambda (x) (not (term-head-is-error x))) (term-subterms term))
        (push term res)))
    res))

;;; NOT USED NOW.
(defun parser-diagnose (module preterm sort)
  (declare (type module module)
           (type list preterm)
           (type sort* sort))
  (if (null preterm)
      (format t "-- !Input is empty~%.")
      (progn
        (print-simple-princ-open preterm) (print-next)
        (let ((prefix nil)
              (suffix preterm)
              (flags (make-list (length preterm)))
              (len (length preterm)))
          (declare (type fixnum len))
          (when *chaos-verbose*
            (princ "[ partial parses ]: ")
            (print-next)
            (let ((indent *print-indent*))
              (declare (type fixnum indent))
              (loop
               (incf indent)
               (let ((*print-indent* indent))
                 (when (null suffix) (return))
                 (when *chaos-verbose*
                   (princ "  ")
                   (when prefix (print-simple-princ-open prefix))
                   (princ " @ ")
                   (when suffix (print-simple-princ-open suffix))
                   (print-next))
                 (let ((res (catch :parse-error
                              (parse-term suffix module
                                          parser-max-precedence ; *******
                                          sort))))
                   (mapc #'(lambda (e)
                             (let ((lenp (length prefix)))
                               (dotimes (i (- len (+ lenp (length (cdr e)))))
                                 (setf (nth (+ lenp i) flags) t)
                                 ))
                             (when *chaos-verbose*
                               (princ "  ==> ")
                               (when prefix
                                 (print-simple-princ-open prefix) (princ " <<< "))
                               (let ((tm (caar e)))
                                 (princ "(")
                                 (term-print tm)
                                 (princ ").")
                                 (print-sort-name (term-sort tm)
                                                  module))
                               (when (cdr e)
                                 (princ " >>> ")
                                 (print-simple-princ-open (cdr e)))
                               (print-next)))
                         res)
                   )
                 (setq prefix (append prefix (list (car suffix))))
                 (setq suffix (cdr suffix))
                 ))))
          (princ "[ partial descriptions ]: ")
          (let ((*print-indent* (+ *print-indent* 2)))
            (print-next)
            (dotimes (i len)
              (if (nth i flags)
                  (princ " !")
                  (progn
                    (princ " ")
                    (princ (nth i preterm)))))
            (print-next)
            (dotimes (i len)
              (if (and (null (nth i flags))
                       (or (= 0 i)
                           (nth (1- i) flags)))
                  (princ " -[")
                  (if (and (not (= 0 i))
                           (nth i flags)
                           (null (nth (1- i) flags)))
                      (princ "]- ")
                      (princ " ")))
              (princ (nth i preterm))
              (print-check))
            (when (null (nth (1- len) flags)) (princ "]-"))
            (print-next)
            ))
        )))

(defun simple-parse-ground (id module preterm  &optional (sort *cosmos*))
  (declare (type t id)
           (type module module)
           (type list preterm)
           (type sort* sort))
  (let ((trm (simple-parse module preterm sort)))
    (unless (term-is-ground? trm)
      (with-output-chaos-warning ()
        (format t "in ~a, term contains variable(s): " id)
        (term-print trm)))
    trm))

;;; parse-convert : term -> term'
;;;
(defun parse-convert (term
                      &optional (module (get-context-module)))
  ;; #define macro expand
  (when *macroexpand*
    (setq term (expand-macro term module)))
  (if *parse-normalize*
      (with-in-module (module)
        (right-associative-normal-form term))
    term))
          
;;; convert builtin constants to appropriate form
;;;  (cond  ((term-is-variable? term) term)
;;;      ((term-is-builtin-constant? term) term)
;;;      (t (re-assign-term-sort term) term))

(defun parse-show-diff (terms)
  (declare (type list terms))
  (let ((*fancy-print* nil)
        ;; (*print-with-sort* t)
        )
    (do* ((term-list terms (cdr term-list))
          (num 1 (1+ num))
          (term (car term-list) (car term-list)))
        ((null term-list))
      (print-next)
      (princ "[") (princ num) (princ "] ")
      (if (term-is-variable? term)
          (print-to-left
           (format nil "variable ~a:~a"
                   (variable-name term)
                   (sort-print-name (term-sort term)))
           "-")
        (if (term-is-builtin-constant? term)
            (print-to-left (bi-method-print-string term) "-")
          (print-to-left (method-print-string (term-head term)) "-")
          )
        )
      (if *chaos-verbose*
          (print-term-tree term t)
        (term-print term) ))))

;;; produces a list of initial complete parses given all parses as arg
;;;
(defun parser-complete-parses (mod parselist)
  (declare (type list parselist))
  (mapcan #'(lambda (x) (if (null (cdr x))
                            (list (parse-convert (caar x) mod))
                            nil))
          parselist))

;;; produces a list of initial complete parses; nil for error
;;;
(defun parser-parses (module preterm &optional (sort *cosmos*))
  (declare (type module module)
           (type (or list string) preterm)
           (type sort* sort))
  (when (stringp preterm)
    (setf preterm (read-term-from-string preterm)))
  (if (null preterm)
      nil
    (with-in-module (module)
      (let ((val (catch :parse-error
                   (parse-term preterm module
                               parser-max-precedence sort)))) ; ****
        (let ((res (mapcan #'(lambda (x) (if (null (cdr x))
                                             (list (parse-convert (caar x)
                                                                  module))
                                           nil))
                           val)))
          (parser-find-parse module res *cosmos* t))))))

;;; takes list of first parses and a sort and comes back with
;;; nil -- none; or a list of possible parses
;;; (any well-defined preferred to ill-defined)
(defun parser-find-parse (module parses sort &optional try-remove-error-method)
  (declare (ignore try-remove-error-method)
           (type module module)
           (type list parses)
           (type sort* sort)
           (type (or null t) try-remove-error-method))
                                        ; optional parameter is not used now,
                                        ; the work is done in pre-choose-final.
                                        ; callers should adapt to  this change.
  (let ((so (module-sort-order module))
        (well nil)
        (p-well nil)
        (any nil)
        (ill nil))
    (declare (type sort-order so)
             (type list well p-well any ill))
    ;; filter out some
    (setq parses (pre-choose-final module parses))
    ;; classify terms:
    ;;  well = well defined & term-sort(term) <= sort.
    ;;  p-well = any well-defined terms of sort belonging the same connected 
    ;;           component with given restriction (considering error-sort).
    ;;  any  = well-defined but not satisfy the sort restriction.
    ;;  ill  = ill-defined terms of any kind.
    (dolist (term parses)
      (if (term-ill-defined term)
          (push term ill)
          (if (sort<= (term-sort term) sort so)
              (push term well)
              (if (is-in-same-connected-component (term-sort term)
                                                  sort
                                                  so)
                  (push term p-well)
                  (push term any)))))
    ;; the precedence is ofcource well > p-well > ill > any
    (or well p-well ill any)))

;;; takes list of first parses and a sort and comes back with
;;; nil -- none; or a list of possible parses
;;; (any well-defined preferred to ill-defined)
;;; very similar to above, but is required to directly satisfy sort restriction
(defun parser-find-parse-strict (module parses sort)
  (declare (type module module)
           (type list parses)
           (type sort* sort))
  (let ((*current-module* module))
    (let ((so (module-sort-order module))
          (ill nil) (well nil))
      (declare (type sort-order so))
      (dolist (tm parses)
        (if (sort<= (term-sort tm) sort so)
            (if (term-ill-defined tm)
                (when (null well) (push tm ill))
                (push tm well))))
      (if well well
          (if ill
              ill
              nil)))))

;;; takes list of first parses and a list of sorts and comes back with
;;; nil -- none; or a list of possible parses
;;; (any well-defined preferred to ill-defined)
;;; very similar to above, but is required to directly satisfy sort restriction
;;;
(defun parser-find-parse-strict-sorts (module parses sorts)
  (declare (type module module)
           (type list parses sorts))
  (let ((*current-module* module))
    (let ((so (module-sort-order module))
          (ill nil) (well nil))
      (declare (type sort-order so))
      (dolist (tm parses)
        (if (member (term-sort tm) sorts
                    :test #'(lambda (x y) (sort<= x y so)))
            (if (term-ill-defined tm)
                (when (null well) (push tm ill))
                (push tm well))))
      (if well
          well
          (if ill
              ill
              nil)))))

;;; given list of parses of lhs and rhs (as from parser-parses) looks
;;; for compatible pair
;;
(defun parser-find-rule-pair (module lhslst rhslst)
  (declare (type module module)
           (type list lhslst rhslst))
  (with-in-module (module)
    (let ((so (module-sort-order module))
          (ok nil)
          (retr nil))
      ;; foreach lhs:lhslst {
      ;;   foreach rhs:rhslst {
      (dolist (lhs lhslst)
        (block cont-lhs
          (when *on-axiom-debug*
            (format t "~%lhs: ")
            (term-print-with-sort lhs))
          (when (term-ill-defined lhs)
            (return-from cont-lhs))     ; skip it and continue
          (let ((sl (term-sort lhs)))
            (dolist (rhs rhslst)
              (block cont-rhs
                (when *on-axiom-debug*
                  (format t "~&rhs: ")
                  (term-print-with-sort rhs))
                (when (term-ill-defined rhs)
                  (return-from cont-rhs)) ; continue it and continue
                (let ((sr (term-sort rhs)))
                  (if (sort<= sr sl so)
                      (push (list lhs rhs) ok)
                    (when (is-in-same-connected-component sl sr so)
                      (push (list lhs rhs) retr)))))))))
      ;; 
      (or ok retr nil))))

;;; used in modexp-compute-op-mapping
;;;
(defun parse-quiet-parse (module preterm &optional (sort *cosmos*))
  (declare (type module module)
           (type list preterm)
           (type sort* sort))
  (if (null preterm)
      (make-bconst-term *syntax-err-sort* '(input empty))
      (with-in-module (module)
        (let ((res (catch :parse-error
                     (parse-term preterm module parser-max-precedence sort)))) ; ****
          (let ((final-well-defined (mapcan #'(lambda (e)
                                                (when (and (null (cdr e))
                                                           (not (term-ill-defined
                                                                 (caar e))))
                                                  (list (caar e))))
                                            res)))
            (let ((final (if final-well-defined final-well-defined
                             (mapcan #'(lambda (e)
                                         (when (null (cdr e)) (list (caar e))))
                                     res))))
              (if (null final)
                  (make-bconst-term *syntax-err-sort* preterm)
                  (let ((raw-parse (car final)))
                    (parse-convert raw-parse module)))))))))



;;;=============================================================================
;;; HOUSE KEEPER
;;;=============================================================================

;;; UPDATE-PARSE-INFORMATION : Module SET[Operator] SET[Variable] -> {cur-mod}
;;; create parse-dictionary, juxtaposition for module
;;; and update sytactic attributes of mehtods.
;;;
(defun token-seq-to-str (tseq)
  (reduce #'(lambda (x y)
              (concatenate 'string x y))
          (mapcar #'(lambda (x)
                      (if (eq x t)
                          "_"
                        x))
                  tseq)))

(defun update-parse-information (module)
  (declare (type module module))
  (let ((opinfos (module-all-operators module))
        (variables (module-variables module)))
    (let ((mod-dict (module-parse-dictionary module)))
      ;; clean up
      (initialize-parse-dictionary mod-dict)
      ;; 
      (dolist (s (module-all-sorts module))
        (when (sort-is-builtin s)
          (dictionary-add-builtin-sort mod-dict s)))
      (dolist (opinfo opinfos)
        (let* ((op (opinfo-operator opinfo))
               (syn-typ (operator-syntactic-type op))
               (token-seq (operator-token-sequence op)))
          (dolist (meth (opinfo-methods opinfo))
            (case syn-typ
              (antefix (dictionary-add-info-on-token mod-dict
                                                     (car token-seq)
                                                     meth))
              (latefix (dictionary-add-info-on-token mod-dict
                                                     (cadr token-seq)
                                                     meth)
                       ;;#||
                       (dictionary-add-info-on-token mod-dict
                                                     (token-seq-to-str token-seq)
                                                     meth)
                       ;;||#
                       )
              (juxtaposition
               ;;#||
               (dictionary-add-info-on-token
                mod-dict
                (token-seq-to-str token-seq)
                meth)
               ;;||#
               (pushnew meth (module-juxtaposition module) :test #'eq))
              (otherwise (break "SNARK: update-parse-information"))))
          ))
      (dolist (var variables)
        (dictionary-add-info-on-token  mod-dict
                                       (string (car var))
                                       (cdr var)))
      (compress-overloaded-methods module mod-dict)
      (setf (module-juxtaposition module)
            (method-compress-overloaded-set (module-juxtaposition module)
                                            (module-sort-order module)))
      ;; set up MACRO rules
      (dolist (macro (module-macros module))
        (setup-macro-rule macro module))
      ;;
      )))

(defun compress-overloaded-methods (module dict)
  (declare (type module module)
           (type parse-dictionary dict))
  (with-in-module (module)
    (let ((table (dictionary-table dict))
          (compressed nil))
      (maphash #'(lambda (ky val)
                   (push (cons ky 
                               (method-compress-overloaded-set val))
                         compressed))
               table)
      ;;
      (dolist (comp compressed)
        (setf (gethash (car comp) table)
              (cdr comp)))
      ;;
      (mapcar #'(lambda (opinfo)
                  (let* ((op (opinfo-operator opinfo))
                         (token-seq (operator-token-sequence op))
                         (key (if (eq t (car token-seq))
                                  (cadr token-seq)
                                  (car token-seq)))
                         (val (gethash key table)))
                    (unless (or (null val)
                                (null (cdr val)))
                      (setf (gethash key table)
                            (method-compress-overloaded-set (gethash key table))))))
              (module-all-operators module))
      )))

;;; ** NOTE: this has side-effects
;;;    (1) updating overloading info on methods (strictly-overloaded).
;;;    (2) 
;;;
#||
(defun method-compress-overloaded-set (items &optional
                                             (sort-order *current-sort-order*)
                                             (opinfo-table *current-opinfo-table*)
                                             (module *current-module*))
                                             
  (let ((methods nil)
        (res nil))
    (dolist (i items)                   ; items may contain vairables
      (if (and (operator-method-p i)
                    (method-arity i))   ; methods with more than 0 arities
          (push i methods)
          (push i res)))
    ;; compress methods
    (dolist (method methods)
      (block next-method
        (let ((meth (method-select-most-general-version-of method
                                                           methods
                                                           sort-order
                                                           opinfo-table
                                                           module)))
          (unless (memq meth res)
            ;; set syntactic properties of the most general method used for parsing,
            ;; we consider `associativity' and `precedence'.
            (when (method-is-error-method meth)
              (let ((ms (method-lower-methods meth)))
                ;; assumption, lower methods (when the mehthod is strictly
                ;; overloaded) are ordered ...
                (when ms
                  (let ((assoc (method-associativity (car ms)))
                        (prec (get-method-precedence (car ms)))
                        (form (method-form (car ms))))
                    (setf (method-associativity meth) assoc)
                    (setf (method-precedence meth) prec)
                    (setf (method-form meth) form)))))
            ;;
            (push meth res)))))
    res))
||#

(defun method-compress-overloaded-set (items &optional
                                             (sort-order *current-sort-order*)
                                             (opinfo-table *current-opinfo-table*)
                                             (module *current-module*))
  (declare (type list items)
           (type sort-order sort-order)
           (type hash-table opinfo-table)
           (type module module))
  ;;
  (let ((methods nil)
        (res nil))
    (dolist (i items)                   ; items may contain vairables
      (if (and (operator-method-p i)
                    (method-arity i))   ; methods with more than 0 arities
          (push i methods)
          (push i res)))
    ;; compress methods
    (dolist (method methods)
      (block next-method
        (let ((meth (method-select-most-general-version-of method
                                                           methods
                                                           sort-order
                                                           opinfo-table
                                                           module)))
          (unless (memq meth res) (push meth res)))))
    ;;
    res))

;;; EOF
