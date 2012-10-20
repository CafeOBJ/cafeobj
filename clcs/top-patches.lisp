
(in-package "CONDITIONS")

(import '(with-simple-restart abort continue compute-restarts
	  *debug-level* *debug-restarts* *number-of-debug-restarts*
	  *debug-abort* *debug-continue* *debug-condition* *debug-eval*
	  find-restart invoke-restart invoke-restart-interactively
	  restart-name ignore-errors show-restarts conditionp)
	"SYSTEM")

(in-package "SYSTEM")

(defvar *abort-restarts* nil)

(defmacro with-clcs-break-level-bindings (&body forms)
  `(let* ((*DEBUG-LEVEL* (1+ *DEBUG-LEVEL*))
	  (debug-level *DEBUG-LEVEL*)
	  (*DEBUG-RESTARTS* (COMPUTE-RESTARTS))
	  (*NUMBER-OF-DEBUG-RESTARTS* (LENGTH *DEBUG-RESTARTS*))
	  (*DEBUG-ABORT*    (FIND-RESTART 'ABORT))
	  (*DEBUG-CONTINUE* (OR (LET ((C (FIND-RESTART 'CONTINUE)))
				  (IF (OR (NOT *DEBUG-CONTINUE*)
					  (NOT (EQ *DEBUG-CONTINUE* C)))
				      C NIL))
				(LET ((C (IF *DEBUG-RESTARTS*
					     (FIRST *DEBUG-RESTARTS*) NIL)))
				  (IF (NOT (EQ C *DEBUG-ABORT*)) C NIL))))
	  (*DEBUG-CONDITION* (if (conditionp at) at *DEBUG-CONDITION*))
	  (*abort-restarts* (let ((abort-list nil))
			      (dolist (restart *DEBUG-RESTARTS*)
				(when (eq 'abort (restart-name restart))
				  (push restart abort-list)))
			      (nreverse abort-list))))
     ,@forms))

(defun clcs-break-level-invoke-restart (-)
  (COND ((AND (PLUSP -)
	      (< - (+ *NUMBER-OF-DEBUG-RESTARTS* 1)))
	 (LET ((RESTART (NTH (- - 1) *DEBUG-RESTARTS*)))
	   (INVOKE-RESTART-INTERACTIVELY RESTART)))
	(T
	 (FORMAT T "~&No such restart."))))

;; From akcl-1-530, changes marked with ;***
(defun clcs-break-level (at &optional env)
  (let* ((*break-message* (if (or (stringp at) (conditionp at)) ;***
			      at *break-message*))  ;***
	 (*quit-tags* (cons (cons *break-level* *quit-tag*) *quit-tags*)) ;***
         (*quit-tag* nil)    ;***
         (*break-level* (if (conditionp at) (cons t *break-level*) *break-level*))
         (*ihs-base* (1+ *ihs-top*))
         (*ihs-top* (1- (ihs-top)))
         (*current-ihs* *ihs-top*)
         (*frs-base* (or (sch-frs-base *frs-top* *ihs-base*) (1+ (frs-top))))
         (*frs-top* (frs-top))
         (*break-env* nil)
	 ;;(be *break-enable*) ;***
	 ;;(*break-enable*               ;***
	  ;;(progn                       ;***
	    ;;(if (stringp at) nil be))) ;***
	 ;;(*standard-input* *terminal-io*)
         (*readtable* (or *break-readtable* *readtable*))
         (*read-suppress* nil)
         (+ +) (++ ++) (+++ +++)
         (- -)
         (* *) (** **) (*** ***)
         (/ /) (// //) (/// ///)
         )
    ;;(terpri *error-output*)
    (with-clcs-break-level-bindings ;***
      (if (consp at)
	  (set-back at env)
	  (with-simple-restart (abort "Return to debug level ~D." DEBUG-LEVEL) ;***
	    (format *debug-io* "~&~A~2%" *break-message*) ;***
	    (when (> (length *link-array*) 0)
	      (format *debug-io* 
		      "Fast links are on: do (use-fast-links nil) for debugging~%"))
	    (set-current)		;***
	    (setq *no-prompt* nil)
	    (show-restarts)))		;***
      (catch-fatal 1)
      (setq *interrupt-enable* t)
      (loop 
       (setq +++ ++ ++ + + -)
       (cond (*no-prompt* (setq *no-prompt* nil))
	     (t
	      (format *debug-io* "~&~a~a>~{~*>~}"
		      (if (stringp at) "" "dbl:")
		      (if (eq *package* (find-package 'user)) ""
			(package-name *package*))
		      *break-level*)))
       (unless ;***
	(with-simple-restart (abort "Return to debug level ~D." DEBUG-LEVEL) ;***
	  (not
	    (catch 'step-continue
	      (setq - (locally (declare (notinline read))
			(dbl-read *debug-io* nil *top-eof*)))
	      (when (eq - *top-eof*) (bye))
	      (let* ( break-command
		     (values
		      (multiple-value-list
			  (LOCALLY (declare (notinline break-call evalhook))
			    (if (or (keywordp -) (integerp -)) ;***
				(setq - (cons - nil)))
			    (cond ((and (consp -) (keywordp (car -)))
				   (setq break-command t)
				   (break-call (car -) (cdr -)))
				  ((and (consp -) (integerp (car -))) ;***
				   (setq break-command t) ;***
				   (clcs-break-level-invoke-restart (car -))) ;***
				  (t (evalhook - nil nil *break-env*))))))) ;***
		(setq /// // // / / values *** ** ** * * (car /))
		(fresh-line *debug-io*)
		(dolist (val /)
		  (locally (declare (notinline prin1)) (prin1 val *debug-io*))
		  (terpri *debug-io*)))
	      nil)))			;***
        (terpri *debug-io*)
        (break-current))))))

(defun clcs-terminal-interrupt (correctablep)
  (if correctablep
      (cerror "Continues execution." "Console interrupt.")
      (error "Console interrupt -- cannot continue.")))

(defun clcs-break-quit (&optional (level 0))
  (let ((abort (nth level (reverse *abort-restarts*))))
    (when abort (invoke-restart-interactively abort)))
  (break-current))

(setq conditions::*debugger-function* 'break-level)
(setq conditions::*debug-command-prefix* "")

(defun break-resume ()
  (and *debug-continue* (invoke-restart *debug-continue*)))

(putprop :r 'break-resume 'break-command)
(putprop :s 'show-restarts 'break-command)

(defun break-help ()
  (format *debug-io* "
Break-loop Command Summary ([] indicates optional arg)
--------------------------

:bl [j]     show local variables and their values, or segment of vs if compiled
              in j stack frames starting at the current one.
:bt [n]     BACKTRACE [n steps]
:down [i]   DOWN i frames (one if no i)
:env        describe ENVIRONMENT of this stack frame (for interpreted).
:fr [n]     show frame n
:loc [i]    return i'th local of this frame if its function is compiled (si::loc i)
:r          RESUME (return from the current break loop).
:up [i]     UP i frames (one if no i)

Example: print a bactrace of the last 4 frames

>>:bt 4

Note:  (use-fast-links nil) makes all non system function calls
be recorded in the stack.   (use-fast-links t) is the default


Low level commands:
------------------
:p [i]           make current the i'th PREVIOUS frame (in list show by :b)
:n [i]           make current the i'th NEXT frame (in list show by :b)
:go [ihs-index]  make current the frame corresponding ihs-index
:m               print the last break message.
:s               show restarts.
:c               show function of the current ihs frame.
:q [i]           quit to top level
:r               resume from this break loop.
:b               full backtrace of all functions and special forms.
:bs [name]       backward search for frame named 'name'
:fs  [name]      search for frame named 'name'
:vs [from] [to]  Show value stack between FROM and TO
:ihs [from] [to] Show Invocation History Stack
:bds ['v1 'v2 ..]Show previous special bindings of v1, v2,.. or all if no v1

")
	  (values)
	  )
