;;; -*- Mode: Lisp; Syntax: Common-Lisp; Base: 10 -*-
(in-package :chaos)

;;;  The external interface is MAKE-PARSER.  It takes three arguments, a
;;;  CFG grammar, a list of the lexical or terminal categories, and an
;;;  atomic end marker.  It produces a list which is the Lisp code for
;;;  an LALR(1) parser for that grammar.  If that list is compiled, then
;;;  the function LALR-PARSER is defined.  LALR-PARSER is a function with 
;;;  two arguments, NEXT-INPUT and PARSE-ERROR. 
;;;
;;;  The first argument to LALR-PARSER, NEXT-INPUT must be a function with 
;;;  zero arguments; every time NEXT-INPUT is called it should return
;;;  a CONS cell, the CAR of which is the category of the next lexical
;;;  form in the input and the CDR of which is the value of that form.
;;;  Each call to NEXT-INPUT should advance one lexical item in the
;;;  input.  When the input is consumed, NEXT-INPUT should return a
;;;  CONS whose CAR is the atomic end marker used in the call to MAKE-PARSER.
;;;
;;;  The second argument to LALR-PARSER, PARSE-ERROR will be called
;;;  if the parse fails because the input is ill-formed.
;;;

(defstruct (grammar)
  (name)
  (engine)
  (glex)
  (grules)
  (gstart)
  (gstarts)
  (gcats)
  (gfirsts)
  (gepsilons)
  (gexpansions)
  (stateList)
  (endmarker))

(defconstant *TOPCAT* '<Start>)

(declaim (special glex grules gstart gstarts gfirsts gepsilons
		  gexpansions statelist *endmarker*
		  *parse-engine*))
(defvar *parse-engine*)
(defvar *ENDMARKER*)
(defvar glex)
(defvar grules)
(defvar gstart)
(defvar gstarts)
(defvar gcats)
(defvar gfirsts)
(defvar gepsilons)
(defvar gexpansions)
(defvar stateList '())
(defvar *lalr-debug* NIL "Inserts debugging code into parser if non-NIL")

(defmacro with-in-grammar ((gram) &body body)
  (once-only (gram)
    ` (let ((glex (grammar-glex ,gram))
	    (grules (grammar-grules ,gram))
	    (gstart (grammar-gstart ,gram))
	    (gstarts (grammar-gstarts ,gram))
	    (gcats (grammar-gcats ,gram))
	    (gfirsts (grammar-gfirsts ,gram))
	    (gepsilons (grammar-gepsilons ,gram))
	    (gexpansions (grammar-gexpansions ,gram))
	    (statelist (grammar-statelist ,gram))
	    (*endmarker* (grammar-endmarker ,gram))
	    (*parse-engine* (grammar-engine ,gram)))
	,@body)))

(defun save-grammar-definition (gram)
  (setf (grammar-glex gram) glex
	(grammar-grules gram) grules
	(grammar-gstart gram) gstart
	(grammar-gstarts gram) gstarts
	(grammar-gcats gram) gcats
	(grammar-gfirsts gram) gfirsts
	(grammar-gepsilons gram) gepsilons
	(grammar-gexpansions gram) gexpansions
	(grammar-statelist gram) statelist
	(grammar-endmarker gram) *endmarker*
	(grammar-engine gram) *parse-engine*)
  gram)

(defun set-grammar (gram)
  (setf glex (grammar-glex gram)
	grules (grammar-grules gram)
	gstart (grammar-gstart gram)
	gstarts (grammar-gstarts gram)
	gcats (grammar-gcats gram)
	gfirsts (grammar-gfirsts gram)
	gepsilons (grammar-gepsilons gram)
	gexpansions (grammar-gexpansions gram)
	statelist (grammar-statelist gram)
	*endmarker* (grammar-endmarker gram)
	*parse-engine* (grammar-engine gram)))
	
;;;
;;; Takes a grammar and produces the parsing engine.
;;;
(defun make-parser (name grammar lex endMarker)
  (let ((gram-def (make-grammar :name name)))
    (setq *ENDMARKER* endMarker)
    (setq glex lex)
    (setq gstart (caar grammar))
    (setq grules (let ((i 0)) 
		   (mapcar #'(lambda (r) (transformRule r (incf i)))
			   grammar)))
    (setq gcats (getallcats))
    (setq gexpansions (mapcar #'(lambda (cat)
				  (cons cat (compute-expansion cat)))
			      gcats))
    (setq gepsilons (remove-if-not #'derivesEps gcats))
    (setq gstarts (cons (list *ENDMARKER* *ENDMARKER*)
			(mapcar #'(lambda (cat)
				    (cons cat (firstTerms (list cat))))
				gcats)))
    ;; now actually build the parser
    (buildTable)
    (when (and (listp *lalr-debug*) (member 'print-table *lalr-debug*))
      (Print-Table stateList))
    (setq *parse-engine* (buildParser))
    (save-grammar-definition gram-def)
    gram-def))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;;;
;;;                    Rules and Grammars
;;;

(defstruct (grule)
  no
  mother
  daughters
  action)

(defun transformRule (grule no)
  (make-grule :no no
	      :mother (first grule)
	      :daughters (butlast (cddr grule))
	      :action (car (last grule))))

(defun compute-expansion (cat)
  (remove-if-not #'(lambda (rule)
                     (eq (grule-mother rule) cat))
                 grules))

(defmacro expand (cat)
  `(cdr (assoc ,cat gexpansions)))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;;;
;;;                    Properties of grammars

(defun GetAllCats ()
  (labels ((try (dejaVu cat)
                (if (find cat dejaVu)
                  dejaVu
                  (tryRules (cons cat dejaVu) (compute-expansion cat))))
           (tryRules (dejaVu rules)
                     (if rules
                       (tryRules (tryCats dejaVu (grule-daughters (car rules)))
                                 (cdr rules))
                       dejaVu))
           (tryCats (dejaVu cats)
                    (if cats
                      (tryCats (try dejaVu (car cats)) (cdr cats))
                      dejaVu)))
    (try '() gstart)))

(defun derivesEps (c)
  "t if c can be rewritten as the null string"
  (labels ((try (dejaVu cat)
             (unless (find cat dejaVu)
               (some #'(lambda (r) 
                         (every #'(lambda (c1) (try (cons cat dejaVu) c1))
                                (grule-daughters r)))
                     (expand cat)))))
    (try '() c)))

(defun derivesEpsilon (c)
  "looks up the cache to see if c derives the null string"
  (member c gepsilons))

(defun FirstTerms (catList)
  "the leading terminals of an expansion of catList"
  (labels ((firstDs (cats)
                    (if cats
                      (if (derivesEpsilon (car cats))
                        (cons (car cats) (firstDs (cdr cats)))
                        (list (car cats)))))
           (try (dejaVu cat)
                (if (member cat dejaVu)
                  dejaVu
                  (tryList (cons cat dejaVu) 
                           (mapcan #'(lambda (r) 
                                       (firstDs (grule-daughters r)))
                                   (expand cat)))))
           (tryList (dejaVu cats)
                    (if cats
                      (tryList (try dejaVu (car cats)) (cdr cats))
                      dejaVu)))
    (remove-if-not #'(lambda (term)
                       (or (eq *ENDMARKER* term)
                           (find term glex))) 
                   (tryList '() (firstDs catList)))))

(defun FirstTerminals (catList)
  (if catList
    (if (derivesEpsilon (first catList))
      (union (cdr (assoc (first catList) gstarts))
             (FirstTerminals (rest catList)))
      (cdr (assoc (first catList) gstarts)))
    '()))


;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;;;
;;;                  LALR(1) parsing table constructor
;;;

(defstruct item rule pos la)

(defmacro item-daughters (i) `(grule-daughters (item-rule ,i)))

(defmacro item-right (i) `(nthcdr (item-pos ,i) (item-daughters ,i)))

(defmacro item-equal (i1 i2)
  `(and (eq (item-rule ,i1) (item-rule ,i2))
        (= (item-pos ,i1) (item-pos ,i2))
        (eq (item-la ,i1) (item-la ,i2))))

(defmacro item-core-equal (c1 c2)
  "T if the cores of c1 and c2 are equal"
  `(and (eq (item-rule ,c1) (item-rule ,c2))
        (= (item-pos ,c1) (item-pos ,c2))))

(defun close-items (items)    
  "computes the closure of a set of items"
  (do ((toDo items))
      ((null toDo) items)
    (let ((i (pop toDo)))
      (when (item-right i)
        (dolist (la (FirstTerminals (append (rest (item-right i))
                                            (list (item-la i)))))
          (dolist (r (expand (first (item-right i))))
              (unless (dolist (i items)
                        (if (and (eq r (item-rule i))
                                 (= (item-pos i) 0)
                                 (eq (item-la i) la))
                          (return t)))
                (let ((new (make-item :rule r :pos 0 :la la)))
                  (push new items)
                  (push new toDo)))))))))

(defun shift-items (items cat)
  "shifts a set of items over cat"
  (labels ((shift-item (item)
                       (if (eq (first (item-right item)) cat)
                         (make-item :rule (item-rule item)
                                    :pos (1+ (item-pos item))
                                    :la (item-la item)))))
    (let ((new-items '()))
      (dolist (i items)
        (let ((n (shift-item i)))
          (if n
            (push n new-items))))
      new-items)))

(defun items-right (items)
  "returns the set of categories appearing to the right of the dot"
  (let ((right '()))
    (dolist (i items)
      (let ((d (first (item-right i))))
        (if (and d (not (find d right)))
          (push d right))))
    right))

(defun compact-items (items)
  "collapses items with the same core to compact items" 
  (let ((soFar '()))
    (dolist (i items)
      (let ((ci (dolist (s soFar)
                  (if (item-core-equal s i)
                    (return s)))))
        (if ci
          (push (item-la i) (item-la ci))
          (push (make-item :rule (item-rule i)
                           :pos (item-pos i)
                           :la (list (item-la i)))
                soFar))))
    (sort soFar #'< 
          :key #'(lambda (i) (grule-no (item-rule i))))))

(defmacro expand-citems (citems)
  "expands a list of compact items into items"
  `(let ((items '()))
     (dolist (ci ,citems)
       (dolist (la (item-la ci))
         (push (make-item :rule (item-rule ci)
                          :pos (item-pos ci)
                          :la la)
               items)))
     items))

(defun subsumes-citems (ci1s ci2s)
  "T if the sorted set of items ci2s subsumes the sorted set ci1s"
  (and (= (length ci1s) (length ci2s))
       (every #'(lambda (ci1 ci2)
                  (and (item-core-equal ci1 ci2)
                       (subsetp (item-la ci1) (item-la ci2))))
              ci1s ci2s)))

(defun merge-citems (ci1s ci2s)
  "Adds the las of ci1s to ci2s.  ci2s should subsume ci1s"
  (mapcar #'(lambda (ci1 ci2)
              (setf (item-la ci2) (nunion (item-la ci1) (item-la ci2))))
          ci1s ci2s)
  ci2s)

;;;  The actual table construction functions

(defstruct state name citems shifts conflict)
(defstruct shift cat where)

(defparameter nextStateNo -1)

;(defun lookup (citems)
;  "finds a state with the same core items as citems if it exits"
;  (find-if #'(lambda (state)
;               (and (= (length citems) (length (state-citems state)))
;                    (every #'(lambda (ci1 ci2)
;                               (item-core-equal ci1 ci2))
;                            citems (state-citems state))
;                    ))
;           stateList))

(defun lookup (citems)
  "finds a state with the same core items as citems if it exits"
  (dolist (state stateList)
    (if (and (= (length citems) (length (state-citems state)))
             (do ((ci1s citems (cdr ci1s))
                  (ci2s (state-citems state) (cdr ci2s)))
                 ((null ci1s) t)
               (unless (item-core-equal (car ci1s) (car ci2s))
                 (return nil))))
      (return state))))

(defun addState (citems)
  "creates a new state and adds it to the state list"
  (let ((newState 
         (make-state :name (intern (format nil "STATE-~D" (incf nextStateNo)))
                     :citems citems)))
    (push newState stateList)
    newState))

(defun getStateName (items)
  "returns the state name for this set of items"
  (let* ((citems (compact-items items))
         (state (lookup citems)))
    (cond ((null state)
           (setq state (addState citems))
           (buildState state items))
          ((subsumes-citems citems (state-citems state))
           nil)
          (t
           (merge-citems citems (state-citems state))
           (followState items)))
    (state-name state)))

      
(defun buildState (state items)
  "creates the states that this state can goto"
  (let ((closure (close-items items)))
    (dolist (cat (items-right closure))
      (push (make-shift :cat cat
                        :where (getStateName (shift-items closure cat)))
            (state-shifts state)))))

(defun followState (items)
  "percolates look-ahead onto descendant states of this state"
  (let ((closure (close-items items)))
    (dolist (cat (items-right closure))
      (getStateName (shift-items closure cat)))))

(defun buildTable ()
  "Actually builds the table"
  (setq stateList '())
  (setq nextStateNo -1)
  (getStateName (list (make-item :rule (make-grule :no 0
						   :mother *TOPCAT*
						   :daughters (list gstart))
                                 :pos 0
                                 :la *ENDMARKER*)))
  (setq stateList (nreverse stateList)))
  
;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;;;
;;;                  LALR(1) parsing table printer
;;;

(defun Print-Table (stateList)
  "Prints the state table"
  (dolist (state stateList)
    (format t "~%~%~a:" (state-name state))
    (dolist (citem (state-citems state))
      (format t "~%  ~a -->~{ ~a~} .~{ ~a~}, ~{~a ~}"
              (grule-mother (item-rule citem))
              (subseq (grule-daughters (item-rule citem)) 0 (item-pos citem))
              (subseq (grule-daughters (item-rule citem)) (item-pos citem))
              (item-la citem)))
    (dolist (shift (state-shifts state))
      (format t "~%    On ~a shift ~a" (shift-cat shift) (shift-where shift)))
    (dolist (reduce (compact-items 
                     (delete-if #'(lambda (i) (item-right i))
                                (close-items 
                                 (expand-citems (state-citems state))))))
      (format t "~%    On~{ ~a~} reduce~{ ~a~} --> ~a"
              (item-la reduce)
              (grule-daughters (item-rule reduce))
              (grule-mother (item-rule reduce)))))
  (format t "~%"))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;;;
;;;                  LALR(1) parser constructor
;;;

(defun translateState (state)
  "translates a state into lisp code that could appear in a labels form"
  (let ((reduces (compact-items 
                  (delete-if #'(lambda (i) (item-right i))
                             (close-items 
                              (expand-citems (state-citems state))))))
        (symbolsSoFar '()))   ; to ensure that a symbol never occurs twice
       (labels ((translateShift (shift)
                                (push (shift-cat shift) symbolsSoFar)
                                `(,(shift-cat shift)
                                  ,@(when *lalr-debug*
                                      `((when *lalr-debug*
                                          (princ ,(format nil "Shift ~a to ~a~%" 
                                                          (shift-cat shift) (shift-where shift))))))
                                  (shift-from #',(state-name state))
                                  (,(shift-where shift))))
                (translateReduce (item)
                                 (when (intersection (item-la item) symbolsSoFar)
                                   (format t "Warning, Not LALR(1)!!: ~a, ~a --> ~{~a ~}~%"
                                           (state-name state) 
                                           (grule-mother (item-rule item))
                                           (grule-daughters (item-rule item)))
                                   (setf (item-la item) 
                                         (nset-difference (item-la item) 
                                                          symbolsSoFar)))
                                 (dolist (la (item-la item))
                                   (push la symbolsSoFar))
                                 `(,(item-la item)
                                   ,@(when *lalr-debug*
                                       `((when *lalr-debug*
                                           (princ ,(format nil "Reduce ~{~a ~} --> ~a~%"
                                                           (grule-daughters (item-rule item))
                                                           (grule-mother (item-rule item)))))))
                                   (reduce-cat #',(state-name state)
                                               ',(grule-mother (item-rule item))
                                               ,(item-pos item)
                                               ,(grule-action (item-rule item))))))
         `(,(state-name state) ()
           (case (input-peek)
             ,@(mapcar #'translateShift (state-shifts state))
             ,@(mapcar #'translateReduce reduces)
             (otherwise (funcall parse-error)))))))

;;;  next-input performs lexical analysis.  It must return a cons cell.
;;;  its car holds the category, its cdr the value.

(defun buildParser ()
  "returns an lalr(1) parser.  next-input must return 2 values!"
  `(lambda (next-input parse-error)
     (let ((cat-la '())          ; category lookahead
           (val-la '())          ; value lookahead
           (val-stack '())       ; value stack
           (state-stack '()))    ; state stack
       (labels ((input-peek ()
                            (unless cat-la
                              (let ((new (funcall next-input)))
                                (setq cat-la (list (car new)))
                                (setq val-la (list (cdr new)))))
                            (first cat-la))
                (shift-from (name)
                            (push name state-stack)
                            (pop cat-la)
                            (push (pop val-la) val-stack))
                (reduce-cat (name cat ndaughters action)
                            (if (eq cat ',*TOPCAT*)
                              (pop val-stack)
                              (let ((daughter-values '())
                                    (state name))
                                (dotimes (i ndaughters)
                                  (push (pop val-stack) daughter-values)
                                  (setq state (pop state-stack)))
                                (push cat cat-la)
                                (push (apply action daughter-values) val-la)
                                (funcall state))))
                ,@(mapcar #'translateState stateList))
         (,(state-name (first stateList)))))))
                
;;; EOF
