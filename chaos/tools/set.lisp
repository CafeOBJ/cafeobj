;;;-*- Mode:LISP; Package:CHAOS; Base:10; Syntax:Common-lisp -*-
;;; $Id: set.lisp,v 1.16 2010-07-15 04:40:55 sawada Exp $
(in-package :chaos)
#|==============================================================================
                                 System: CHAOS
                                 Module: tools
                                 File: set.lisp
==============================================================================|#
#-:chaos-debug
(declaim (optimize (speed 3) (safety 0) #-GCL (debug 0)))
#+:chaos-debug
(declaim (optimize (speed 1) (safety 3) #-GCL (debug 3)))

;;;-----------------------------------------------------------------------------
;;; SET COMMAND Handlers
;;;-----------------------------------------------------------------------------

;;; (key (list_of_sub_key) 'parity global-var doc-string [on-proc off-proc])
;;; (key (list_of_sub_key) 'general global-var doc-string set-proc)

(defmacro chaos-switch-key (sw)
  `(car ,sw))
(defmacro chaos-switch-subkey (sw)
  `(cadr ,sw))
(defmacro chaos-switch-type (sw)
  `(caddr ,sw))
(defmacro chaos-switch-var (sw)
  `(cadddr ,sw))
(defmacro chaos-switch-doc (sw)
  `(fifth ,sw))
(defmacro chaos-switch-on-proc (sw)
  `(sixth ,sw))
(defmacro chaos-switch-off-proc (sw)
  `(seventh ,sw))
(defmacro chaos-switch-set-proc (sw)
  `(sixth ,sw))
(defmacro chaos-switch-hidden (sw)
  `(eighth ,sw))

(defparameter *chaos-switches*
    '((:comment "** rewriting -------------------------------------------")
      ("trace" ("whole") parity $$trace-rewrite-whole "trace rewrite step."
       trace-whole-on
       trace-whole-off)
      ("trace" nil parity $$trace-rewrite "trace every rewrite step."
       trace-on
       trace-off)
      ("step" nil parity *rewrite-stepping* "stepwise rewriting process." step-on step-off)
      ("memo" nil parity *memo-rewrite* "enable term memoization.")
      ("always" ("memo") parity *always-memo*
       "implicitly set 'memo' attributes to user defined operators.")
      ("clean" ("memo") parity *clean-memo-in-normalize*
       "clean up term memo table before normalization.")
      (("statistics" "stats")
       nil parity *show-stats* "show statistics data after reduction.")
      (("rewrite" "rwt") ("limit") general *rewrite-count-limit*
       "maximum number of rewriting."
       set-rewrite-count-limit2)
      ("stop" ("pattern") general *rewrite-stop-pattern*
       "stop rewriting when meets pattern(term)."
       set-rewrite-stop-pattern2)
      ;; ("mel" ("sort") parity *mel-sort*
      ;; "compute result sort with sort membership predicates.")
      ;; ("mel" ("always") parity *mel-always*
      ;; "apply sort memb predicates even the result is of non-error sort.")
      ("reduce" ("conditions") parity *reduce-conditions*
       "reduce condition part in \"apply\" command.")
      ;; ("allow" ("$$term") parity *allow-$$term*
      ;; "allow using \"$$term\" or \"$$subterm\"")
      ("exec" ("trace") parity *cexec-trace*
       "if on, trace concurrent execution.")
      ("exec" ("limit") general *cexec-limit*
       "limit maximum number of concurrent execution."
       chaos-set-cexec-limit)
      ;; ("exec" ("normalize") parity *cexec-normalize*
      ;;  "if on, reduce term before and after each transition.")
      ;; ("exec" ("all") parity *cexec-find-all-solutions*
      ;;  "if on, find all solutions of =(*)=>.")
      (:comment "** system behaviour control ----------------------------")
      ("include" ("BOOL") parity *include-BOOL* "import BOOL implicitly.")
      ("include" ("RWL") parity *include-rwl* "import RWL implicitly.")
      #+:bigpink
      ("include" ("FOPL-CLAUSE") parity *include-fopl* "import FOPL-CLAUSE implicitly.")
      ;; ("stats" nil parity *show-stats* "abbribiation of `statistics'.")
      ("auto" ("context")  parity *auto-context-change*
       "automatic change current context(module).")
      ;; ("auto" ("reconstruct") parity *auto-reconstruct*
      ;;  "perform automatic reconstruction of modules if inconsistent.")
      ;; ("accept" ("term") parity *allow-general-term-input*
      ;; "allow input term directly at top level.")
      (("regularize" "reg") ("signature") parity *regularize-signature*
       "regularize module signature automatic.")
      ("check" ("import") parity *check-import-mode*
       "check conflicting importing mode of submodules.")
      ("check" ("regularity") parity *check-regularity*
       "perform regularity check of signatures in automatic.")
      ("check" ("coherency") parity *check-rwl-coherency*
       "check transitions and equations are coherent or not in automatic.")
      ("check" ("sensible") parity *check-sensibleness*
       "check if sigunature is sensible in automatic.")
      ("check" ("compatibility") parity *check-compatibility*
       "perform compatibility check of TRS in automatic.")
      ;; ("check" ("builtin") parity *builtin-overloading-check*
      ;; "perform operator overloading check with builtin sorts.")
      ;; ("select" ("term") parity *select-ambig-term*
      ;;  "allow users to select a term from anbiguously parsed terms.")
      ("verbose" nil parity *chaos-verbose* "set verbose mode." set-verbose-on set-verbose-off)
      ("quiet" () parity *chaos-quiet* "be quiet." set-quiet-on set-quiet-off)
      (:comment "** show/display options --------------------------------")
      ("all" ("axioms") parity *print-all-eqns* "print all axioms in \"show <Modexp>\"")
      ;; ("all" ("rules") parity *module-all-rules-every* 
      ;;  "print all rules in \"show rules\" command.")
      ("show" ("mode") general *show-mode*
       "set syntax of printed modules or views, .e.t.c. ~~value is either :cafeobj or :meta."
       chaos-set-show-mode)
      ("show" ("var" "sorts") parity *print-with-sort* 
       "if on, variables are printed with their sorts.")
      ("print" ("mode") general *print-xmode*
       "set term print form, one of :normal, :fancy, :tree or :s-expr."
       chaos-set-print-mode)
      ("print" ("depth") general *term-print-depth*
       "max depth of terms to be printed."
       chaos-set-print-depth)
      (:comment "** misc settings ---------------------------------------")
      ("libpath" () general *chaos-libpath*
       "set file search path. `set libpath + path-list' adds search path."
       chaos-set-search-path)
      ;; (("tram" "compiler") ("path") general *tram-path*
      ;; "pathname to TRAM compiler."
      ;; chaos-set-tram-path)
      ;; (("tram" "compiler") ("options") general *tram-options*
      ;; "optional arguments to TRAM cmpiler."
      ;; chaos-set-tram-options)
      ("accept" ("=*=" "proof") parity *accept-system-proof*
       "accept system's automatic proof of congruency of =*=.")
      ("find" ("all" "rules") parity *find-all-rules*
       "find rewrite rules for all occurrences of given term in 'find' command.")
      (:comment "** old switches (obsolete) ----------------------------")
      ("print" ("fancy") general *fancy-print*
       "this switch is obsolete. please use `print mode' switch instead."
       chaos-obsolete-print-fancy)
      ;; *patch* Tue Nov  4 15:40:26 JST 2003; sawada@sra.co.jp
      ("tree" ("print") general *print-term-struct* 
       "terms are printed in a form of parse tree. this flag precedes `print s-expr'.
NOTE: this switch is obsolete now. please use `print mode' switch instead."
       chaos-obsolete-print-tree)
      ;; followings are hidden switches
      ("fast" ("parse") parity *fast-parse*
       "if set on, term parser runs faster but produces much less info on error."
       nil nil t)
      ("cond" ("limit") general *condition-trial-limit*
       "maximum number of trials of evaluating rule condition."
       set-cond-trial-limit
       nil t)                           ; this is hidden
      ("parse" ("normalize") parity *parse-normalize*
       "if set on, terms with associative operators are always parsed as right assocative."
       nil nil t)
      ;; USER DEFINED BOOL
      ("BOOL" ("=") general *user-bool*
       "set path of user defined \"BOOL\" module."
       chaos-set-bool-path)
      ;; debug flags : invisible from user, internal use only
      ("sys" ("universal-sort") parity *allow-universal-sort* "" nil nil t)
      ("debug" ("rewrite") parity *rewrite-debug* "" nil nil t)
      ("debug" ("hash") parity *on-term-hash-debug* "" nil nil t)
      ("debug" ("axiom") parity *on-axiom-debug* "" nil nil t)
      ("debug" ("beh") parity *beh-debug* "" nil nil t)
      ("debug" ("rule") parity *gen-rule-debug* "" nil nil t)
      ("debug" ("change") parity *on-change-debug* "" nil nil t)
      ("debug" ("operator") parity *on-operator-debug* "" nil nil t)
      ("debug" ("sort") parity *on-sort-debug* "" nil nil t)
      ("debug" ("trs") parity *on-trs-debug* "" nil nil t)
      ("debug" ("import") parity *on-import-debug* "" nil nil t)
      ("debug" ("modexp") parity *on-modexp-debug* "" nil nil t)
      ("debug" ("view") parity *on-view-debug* "" nil nil t)
      ("debug" ("match") parity *match-debug* "" nil nil t)
      ("debug" ("dep") parity *module-dep-debug* "" nil nil t)
      ("debug" ("term") parity *term-debug* "" nil nil t)
      ("debug" ("parse") parity *on-parse-debug* "" nil nil t)
      ("debug" ("regularize") parity *regularize-debug* "" nil nil t)
      ("debug" ("tram") parity *on-tram-debug* "" nil nil t)
      ("debug" ("mel") parity *mel-debug* "" nil nil t)
      ("debug" ("exec") parity *cexec-debug* "" nil nil t)
      ("debug" ("apply") parity *apply-debug* "" nil nil t)
      ("debug" ("meta") parity *debug-meta* "" nil nil t)
      ;;
      ("m-and-also" () general nil "" set-m-and-also nil t)
      ))

(defun set-chaos-switch (which value)
  (if (equal which "?")
      (print-set-help)
    (progn 
      (dolist (sw *chaos-switches*)
        (block next
          (let ((dat value)
                (key (chaos-switch-key sw)))
            (when (eq key :comment) (return-from next nil))
            (when (atom key) (setq key (list key)))
            ;; match key & subkey
            (block fail
              (when (member which key :test #'equal)
                (let ((opt (chaos-switch-subkey sw)))
                  (if (equal opt (firstn value (length opt)))
                      (setq dat (nthcdr (length opt) value))
                    (return-from fail nil)))
                (case (chaos-switch-type sw)
                  (parity 
                   (catch 'parity-error
                     (let ((parity (check-parity (car dat))))
                       (let ((on-proc (chaos-switch-on-proc sw))
                             (off-proc (chaos-switch-off-proc sw)))
                         (cond ((and parity on-proc) (funcall on-proc))
                               ((and (null parity) off-proc) (funcall off-proc))
                               (t (set (chaos-switch-var sw) parity)))))
                     (return-from set-chaos-switch t)))
                  (otherwise            ; general value
                   (funcall (chaos-switch-set-proc sw) dat)
                   (return-from set-chaos-switch t))))))))
      (with-output-chaos-warning ()
        (format t "unknown switch for `set' command : ~{~^ ~a~}" (cons which value)))
      nil)))

(defun check-parity (x)
  (if (or (equal "on" x)
          (equal "yes" x))
      t
    (if (or (equal "off" x) (equal "no" x))
        nil
	  (progn
	    (princ "Specify on(yes) or off(no).") (terpri)
	    (throw 'parity-error nil)))))


(defun show-modes (flg)
  (if (eq flg t)
      (let ((*print-line-limit* 62))
        (format t "~%switch~24Tvalue~%--------------------------------------------------------------")
        (dolist (sw *chaos-switches*)
          (unless (chaos-switch-hidden sw)
            (show-mode sw))))
    (let ((sw flg))
      (if (or (equal sw '(".")) (null sw))
          (show-modes t)
	    (let ((which (car flg))
              (sub (cdr flg))
              (found nil)
              (cand nil))
	      (dolist (sw *chaos-switches*)
            (block next
              (let ((key (chaos-switch-key sw)))
                (when (eq key :comment) (return-from next nil))
                (when (atom key) (setq key (list key)))
                (when (member which key :test #'equal)
                  (setq cand sw)
                  (let ((opt (chaos-switch-subkey sw)))
                    (when (equal opt (firstn sub (length opt)))
                      (setq found sw)
                      (setq cand nil)
                      (return)))))))
	      (unless (or found cand)
            (with-output-chaos-warning ()
              (format t "unknown switch ~a" flg)
              (return-from show-modes nil)))
	      (if found
              (show-mode found)
            (show-mode cand)))))))

(defun show-mode (switch)
  (let ((name (chaos-switch-key switch))
        (option (chaos-switch-subkey switch))
        (value (symbol-value (chaos-switch-var switch)))
        (type (chaos-switch-type switch)))
    (cond ((eq name :comment)
           (format t "~%~a" (second switch)))
          (t (when (atom name) (setq name (list name)))
             (if (eq type 'parity)
                 (format t "~&~{~a~^|~a~} ~{~^ ~a~} ~24T~:[off~;on~]" name option value)
               (progn (format t "~&~{~a~^|~a~} ~{~^ ~a~} ~24T= " name option)
                      (if value
                          (print-chaos-object value)
                        (princ "not specified"))))))))

(defun print-set-help ()
  (dolist (sw *chaos-switches*)
    (unless (chaos-switch-hidden sw)
      (let ((key (chaos-switch-key sw)))
        (cond ((eq key :comment)
               (format t "~%~a" (second sw)))
              (t (when (atom key) (setq key (list key)))
                 (case (chaos-switch-type sw)
                   (parity
                    (format t "~& set ~{~a~^|~a~}~{~^ ~a~} {on|off} : ~a"
                            key
                            (chaos-switch-subkey sw)
                            (chaos-switch-doc sw)))
                   (otherwise (format t "~& set ~{~a~^|~a~}~{~^ ~a~} <value> : ~a"
                                      key
                                      (chaos-switch-subkey sw)
                                      (chaos-switch-doc sw))))))))))

;;;
;;; Save/Restore Utilities
;;; ******* TODO:::::::::::::::::::::::::::::::::::
(defun save-switches (name) name)

(defun restore-switches (name) name)

(defun save-switch (sw-name to-where) sw-name to-where)

(defun restore-switch (sw-name from-where) sw-name from-where)

;;;
;;; some switch setters
;;;
(defun chaos-set-search-path (path)
  (let* ((add (if (equal "+" (car path))
                  t
                nil))
         (paths (if add (cadr path) (car path))))
    (if add
        (set-search-path-plus paths)
      (set-search-path paths))))

(defun chaos-set-tram-path (path)
  (let ((path (car path)))
    (when (consp path)
      (setq path (car path)))
    (setq *tram-path* path)
    (kill-tram-process)))

(defun chaos-set-tram-options (options)
  (if options
      (setq *tram-options* (reduce #'(lambda (x y) (concatenate 'string x " " y))
                                   options))
    (setq *tram-options* "")))

(defun chaos-set-show-mode (value)
  (case-equal (car value)
              ((":meta" ":chaos" "chaos")
               (setq *show-mode* :chaos))
              ((":cafeobj" "cafeobj")
               (setq *show-mode* :cafeobj))
              (otherwise
               (with-output-chaos-error ('invalid-value)
                 (format t "value must be either `cafeobj' or `meta'")))))

(defun chaos-set-cexec-limit (value)
  (if (or (null value)
          (equal value '(".")))
      (setq *cexec-limit* most-positive-fixnum)
    (multiple-value-bind (num len)
        (parse-integer (car value) :junk-allowed t)
      (if (= len (length (car value)))
          (setq *cexec-limit* num)
	    (with-output-chaos-error ('invalid-value)
	      (format t "invalid value for exec limit: ~a" (car value))
	      (print-next)
	      (princ "must be a positive integer.") )))))

(defun chaos-set-print-depth (value)
  (if (or (null value)
          (equal value '(".")))
      (setq *term-print-depth* nil)
    (multiple-value-bind (num len)
        (parse-integer (car value) :junk-allowed t)
      (if (= len (length (car value)))
          (setq *term-print-depth* num)
	    (with-output-chaos-error ('invalid-value)
	      (format t "invalid value for term print depth: ~a" (car value))
	      (print-next)
	      (princ "must be a positive integer."))))))

(defun chaos-set-print-mode (value)
  (case-equal (car value)
              ((":fancy" "fancy") (setq *print-xmode* :fancy))
              ((":tree" "tree") (setq *print-xmode* :tree))
              ((":s-expr" "s-expr") (setq *print-xmode* :s-expr))
              ((nil ":normal" "normal")
               (setq *print-xmode* :normal))
              (otherwise
               (with-output-chaos-error ('invalid-value)
                 (format t "invalid value for print mode ~a" (car value))
                 (print-next)
                 (princ "specify one of `normal' `fancy' `tree' or `s-expr'.")))))

(defun chaos-obsolete-print-fancy (value)
  (declare (ignore value))
  (with-output-chaos-warning ()
    (format t "`set print fancy { on | off }' is now obsolete.")
    (print-next)
    (format t "please use `set print mode fancy' or `print mode normal'.")))

(defun chaos-obsolete-print-tree (value)
  (declare (ignore value))
  (with-output-chaos-warning ()
    (format t "sorry but `set tree print { on | off }' is obsolete now.")
    (print-next)
    (format t "please use `set print mode tree' for printing parse tree.")
    (print-next)
    (format t "other settings of `print mode' switch are :fancy and :normal.")))

;;;
(defun chaos-set-bool-path (path)
  (let ((path (car path)))
    (when (consp path)
      (setq path (car path)))
    (setq *user-bool* path)))

;;;
(defun set-m-and-also (value)
  (cond ((string= (car value) "on")
	 (setq *m-and-op* *bool-and-also*)
	 (setq *m-or-op* *bool-or-else*))
	(t
	 (setq *m-and-op* *bool-and*)
	 (setq *m-or-op* *bool-or-else*))))

;;; EOF

