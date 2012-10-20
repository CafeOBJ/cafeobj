;;;-*- Mode:LISP; Package:CHAOS; Base:10; Syntax:Common-lisp -*-
;;; $Id: lex.lisp,v 1.1.1.1 2003-06-19 08:30:34 sawada Exp $
(in-package :pg)
#|==============================================================================
				  System:PG
				 File: lex.lisp
==============================================================================|#
#-:pg-debug
(declaim (optimize (speed 3) (safety 0) #-GCL (debug 0)))
#+:pg-debug
(declaim (optimize (speed 1) (safety 3) #-GCL (debug 3)))

;;; ****************
;;; REGEXPR COMPILER
;;; ****************

(defvar *regex-groups* (make-array 10))
(defvar *regex-groupings* 0)
(defvar .regexp-matcher-hash. (make-hash-table :test #'equal))
(defvar *regex-special-chars* "?*+.()[]\\${}")

(defmacro add-exp (list)
  "Add an item to the end of expression"
  `(setf expression (append expression ,list)))

(defun is-simple-string-pattern? (regexpr)
  (declare (ignore regexpr))
  nil)

(defun make-regexp-matcher (regexpr)
  (or (gethash regexpr .regexp-matcher-hash.)
      (let (fun)
	(setf fun
	      (let ((matcher (regex-compile regexpr :anchored t)))
					; always anchored
		`(lambda (expr)
		   (let ((result nil))
		     (if (funcall (function ,matcher) expr)
			 (if (= *regex-groupings* 0)
			     t
			     (dotimes (i *regex-groupings* result)
			       (push (aref *regex-groups* i)
				     result)))
			 nil)))))
	(setf fun (compile nil fun))
	(setf (gethash regexpr .regexp-matcher-hash.) fun)
	fun)))

;;;  Usage: (regex-compile <expression> [ :anchored (t/nil) ])
;;;       This function take a regular expression (supplied as source) and
;;;       compiles this into a lambda list that a string argument can then
;;;       be applied to.  It is also possible to compile this lambda list
;;;       for better performance or to save it as a named function for later
;;;       use
(defun regex-compile (source &key (anchored nil))
  ;; This routine works in two parts.
  ;; The first pass take the regular expression and produces a list of 
  ;; operators and lisp expressions for the entire regular expression.  
  ;; The second pass takes this list and produces the lambda expression.
  (let ((expression '())		; holder for expressions
	(group 1)			; Current group index
	(group-stack nil)		; Stack of current group endings
	(result nil)			; holder for built expression.
	(fast-first nil))		; holder for quick unanchored scan
    ;;
    ;; If the expression was an empty string then it alway
    ;; matches (so lets leave early)
    ;;
    (if (= (length source) 0)
	(return-from regex-compile
		     '(lambda (&rest args)
			(declare (ignore args))
			t)))
    ;;
    ;; If the first character is a caret then set the anchored
    ;; flags and remove if from the expression string.
    ;;
    (cond ((eql (char source 0) #\^)
	   (setf source (subseq source 1))
	   (setf anchored t)))
    ;;
    ;; If the first sequence is .* then also set the anchored flags.
    ;; (This is purely for optimization, it will work without this).
    ;;
    (if (>= (length source) 2)
	(if (string= source ".*" :start1 0 :end1 2)
	    (setf anchored t)))
    ;;
    ;; Also, If this is not an anchored search and the first character is
    ;; a literal, then do a quick scan to see if it is even in the string.
    ;; If not then we can issue a quick nil, 
    ;; otherwise we can start the search at the matching character to skip
    ;; the checks of the non-matching characters anyway.
    ;;
    ;; If I really wanted to speed up this section of code it would be 
    ;; easy to recognize the case of a fairly long multi-character literal
    ;; and generate a Boyer-Moore search for the entire literal. 
    ;;
    ;; I generate the code to do a loop because on CMU Lisp this is about
    ;; twice as fast a calling position.
    ;;
    (if (and (not anchored)
	     (not (position (char source 0) *regex-special-chars*))
	     (not (and (> (length source) 1)
		       (position (char source 1) *regex-special-chars*))))
	(setf fast-first `((if (not (dotimes (i length nil)
				     (if (eql (char string i)
					      ,(char source 0))
					 (return (setf start i)))))
			      (return-from final-return nil)))))
    ;;
    ;; Generate the very first expression to save the starting index
    ;; so that group 0 will be the entire string matched always
    ;;
    (add-exp '((setf (aref *regex-groups* 0)
		     (list index nil))))
    ;;
    ;; Loop over each character in the regular expression building the
    ;; expression list as we go.
    ;;
    (do ((eindex 0 (1+ eindex)))
	((= eindex (length source)))
      (let ((current (char source eindex)))
	(case current
	  ((#\.)
	   ;;
	   ;; Generate code for a single wild character
	   ;;
	   (add-exp '((if (>= index length)
			  (return-from compare nil)
			(incf index)))))
	  ((#\$)
	   ;;
	   ;; If this is the last character of the expression then
	   ;; anchor the end of the expression, otherwise let it slide
	   ;; as a standard character (even though it should be quoted).
	   ;;
	   (if (= eindex (1- (length source)))
	       (add-exp '((if (not (= index length))
			      (return-from compare nil))))
	     (add-exp '((if (not (and (< index length)
				      (eql (char string index) #\$)))
			    (return-from compare nil)
			  (incf index))))))
	  ((#\*)
	   (add-exp '(ASTRISK)))

	  ((#\+)
	   (add-exp '(PLUS)))

	  ((#\?)
	   (add-exp '(QUESTION)))

	  ((#\()
	   ;;
	   ;; Start a grouping.
	   ;;
	   (incf group)
	   (push group group-stack)
	   (add-exp `((setf (aref *regex-groups* ,(1- group)) 
			    (list index nil))))
	   (add-exp `(,group)))
	  ((#\))
	   ;;
	   ;; End a grouping
	   ;;
	   (let ((group (pop group-stack)))
	     (add-exp `((setf (cadr (aref *regex-groups* ,(1- group)))
			      index)))
	     (add-exp `(,(- group)))))
	  ((#\[)
	   ;;
	   ;; Start of a range operation.
	   ;; Generate a bit-vector that has one bit per possible character
	   ;; and then on each character or range, set the possible bits.
	   ;;
	   ;; If the first character is carat then invert the set.
	   (let* ((invert (eql (char source (1+ eindex)) #\^))
		  (bitstring (make-array 256 :element-type 'bit
					     :initial-element
					        (if invert 1 0)))
		  (set-char (if invert 0 1)))
	     (if invert (incf eindex))
	     (do ((x (1+ eindex) (1+ x)))
		 ((eql (char source x) #\]) (setf eindex x))
	       (cond ((and (eql (char source (1+ x)) #\-)
			   (not (eql (char source (+ x 2)) #\])))
		      (if (>= (char-code (char source x))
			     (char-code (char source (+ 2 x))))
			  (error "Invalid range \"~A-~A\".  Ranges must be in acending order"
				 (char source x) (char source (+ 2 x))))
		      (do ((j (char-code (char source x)) (1+ j)))
		       ((> j (char-code (char source (+ 2 x))))
			(incf x 2))
		     (setf (sbit bitstring j) set-char)))
		     (t
		      (cond ((not (eql (char source x) #\]))
			     (let ((char (char source x)))
			       ;;
			       ;; If the character is quoted then find out what
			       ;; it should have been
			       ;;
			       (if (eql (char source x) #\\ )
				   (let ((length))
				     (multiple-value-setq (char length)
					 (regex-quoted (subseq source x) invert))
				     (incf x length)))
			       (if (not (vectorp char))
				   (setf (sbit bitstring (char-code (char source x))) set-char)
				 (bit-ior bitstring char t))))))))
	     (add-exp `((let ((range ,bitstring))
			  (if (>= index length)
			      (return-from compare nil))
			  (if (= 1 (sbit range (char-code (char string index))))
			      (incf index)
			    (return-from compare nil)))))))
	  ((#\\ )
	   ;;
	   ;; Intreprete the next character as a special, range, octal, group or 
           ;; just the character itself.
	   ;;
	   (let ((length)
		 (value))
	     (multiple-value-setq (value length)
		 (regex-quoted (subseq source (1+ eindex)) nil))
	     (cond ((listp value)
		    (add-exp value))
		   ((characterp value)
		    (add-exp `((if (not (and (< index length)
					     (eql (char string index) 
						  ,value)))
				   (return-from compare nil)
				 (incf index)))))
		   ((vectorp value)
		    (add-exp `((let ((range ,value))
				 (if (>= index length)
				     (return-from compare nil))
				 (if (= 1 (sbit range (char-code (char string index))))
				     (incf index)
				   (return-from compare nil)))))))
	     (incf eindex length)))
	  (t
	   ;;
	   ;; We have a literal character.  
	   ;; Scan to see how many we have and if it is more than one
	   ;; generate a string= verses as single eql.
	   ;;
	   (let* ((lit "")
		  (term (dotimes (litindex (- (length source) eindex) nil)
			  (let ((litchar (char source (+ eindex litindex))))
			    (if (position litchar *regex-special-chars*)
				(return litchar)
			      (progn
				(setf lit (concatenate 'string lit 
						       (string litchar)))))))))
	     (if (= (length lit) 1)
		 (add-exp `((if (not (and (< index length)
					  (eql (char string index) ,current)))
				(return-from compare nil)
			      (incf index))))
	       ;;
	       ;; If we have a multi-character literal then we must
	       ;; check to see if the next character (if there is one)
	       ;; is an astrisk or a plus.  If so then we must not use this
	       ;; character in the big literal.
	       (progn 
		 (if (or (eql term #\*) (eql term #\+))
		     (setf lit (subseq lit 0 (1- (length lit)))))
		 (add-exp `((if (< length (+ index ,(length lit)))
				(return-from compare nil))
			    (if (not (string= string ,lit :start1 index
					      :end1 (+ index ,(length lit))))
				(return-from compare nil)
			      (incf index ,(length lit)))))))
	     (incf eindex (1- (length lit))))))))
    ;;
    ;; Plug end of list to return t.  If we made it this far then
    ;; We have matched!
    (add-exp '((setf (cadr (aref *regex-groups* 0))
		     index)))
    (add-exp '((return-from final-return t)))
    ;;
    ;;
    ;; Now take the expression list and turn it into a lambda expression
    ;; replacing the special flags with lisp code.
    ;; For example:  A BEGIN needs to be replace by an expression that
    ;; saves the current index, then evaluates everything till it gets to
    ;; the END then save the new index if it didn't fail.
    ;; On an ASTRISK I need to take the previous expression and wrap
    ;; it in a do that will evaluate the expression till an error
    ;; occurs and then another do that encompases the remainder of the
    ;; regular expression and iterates decrementing the index by one
    ;; of the matched expression sizes and then returns nil.  After
    ;; the last expression insert a form that does a return t so that
    ;; if the entire nested sub-expression succeeds then the loop
    ;; is broken manually.
    ;; 
    (setf result (copy-tree nil))
    ;;
    ;; Reversing the current expression makes building up the 
    ;; lambda list easier due to the nexting of expressions when 
    ;; and astrisk has been encountered.
    (setf expression (reverse expression))
    (do ((elt 0 (1+ elt)))
	((>= elt (length expression)))
      (let ((piece (nth elt expression)))
	;;
	;; Now check for PLUS, if so then ditto the expression and then let the
	;; ASTRISK below handle the rest.
	;;
	(cond ((eql piece 'PLUS)
	       (cond ((listp (nth (1+ elt) expression))
		      (setf result (append (list (nth (1+ elt) expression))
					   result)))
		     ;;
		     ;; duplicate the entire group
		     ;; NOTE: This hasn't been implemented yet!!
		     (t
		      (format *standard-output* "GROUP repeat hasn't been implemented yet~%")))))
	(cond ((listp piece)		;Just append the list
	       (setf result (append (list piece) result)))
	      ((eql piece 'QUESTION)	; Wrap it in a block that won't fail
	       (cond ((listp (nth (1+ elt) expression))
		      (setf result 
			    (append `((progn (block compare
						    ,(nth (1+ elt) 
							  expression))
					     t))
				    result))
		      (incf elt))
		     ;;
		     ;; This is a QUESTION on an entire group which
		     ;; hasn't been implemented yet!!!
		     ;;
		     (t
		      (format *standard-output* "Optional groups not implemented yet~%"))))
	      ((or (eql piece 'ASTRISK) ; Do the wild thing!
		   (eql piece 'PLUS))
	       (cond ((listp (nth (1+ elt) expression))
		      ;;
		      ;; This is a single character wild card so
		      ;; do the simple form.
		      ;;
		      (setf result 
			    `((let ((oindex index))
				(block compare
				       (do ()
					   (nil)
					 ,(nth (1+ elt) expression)))
				(do ((start index (1- start)))
				    ((< start oindex) nil)
				  (let ((index start))
				    (block compare
					   ,@result))))))
		      (incf elt))
		     (t
		      ;;
		      ;; This is a subgroup repeated so I must build
		      ;; the loop using several values.
		      ;;
		      ))
	       )
	      (t t))))			; Just ignore everything else.
    ;;
    ;; Now wrap the result in a lambda list that can then be 
    ;; invoked or compiled, however the user wishes.
    ;;
    (if anchored
	(setf result
	      `(lambda (string &key (start 0) (end (length string)))
		 (setf *regex-groupings* ,group)
		 (block final-return
			(block compare
			       (let ((index start)
				     (length end))
				 ,@result)))))
      (setf result
	    `(lambda (string &key (start 0) (end (length string)))
	       (setf *regex-groupings* ,group)
	       (block final-return
		      (let ((length end))
			,@fast-first
			(do ((marker start (1+ marker)))
			    ((> marker end) nil)
			  (let ((index marker))
			    (if (block compare
				       ,@result)
				(return t)))))))))
    result
    ))

;;;
;;; Define a function that will take a quoted character and return
;;; what the real character should be plus how much of the source
;;; string was used.  If the result is a set of characters, return an
;;; array of bits indicating which characters should be set.  If the
;;; expression is one of the sub-group matches return a
;;; list-expression that will provide the match.  
;;;
(defun regex-quoted (char-string &optional (invert nil))
  "Usage: (regex-quoted <char-string> &optional invert)
       Returns either the quoted character or a simple bit vector of bits set for
       the matching values"
  (let ((first (char char-string 0))
	(result (char char-string 0))
	(used-length 1))
    (cond ((eql first #\n)
	   (setf result #\NewLine))
	  ((eql first #\c)
	   (setf result #\Return))
	  ((eql first #\t)
	   (setf result #\Tab))
	  ((eql first #\d)
	   (setf result #*0000000000000000000000000000000000000000000000001111111111000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000))
	  ((eql first #\D)
	   (setf result #*1111111111111111111111111111111111111111111111110000000000111111111111111111111111111111111111111111111111111111111111111111111111111111111111111111111111111111111111111111111111111111111111111111111111111111111111111111111111111111111111111111111111111111))
	  ((eql first #\w)
	   (setf result #*0000000000000000000000000000000000000000000000001111111111000000011111111111111111111111111000010111111111111111111111111110000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000))
	  ((eql first #\W)
	   (setf result #*1111111111111111111111111111111111111111111111110000000000111111100000000000000000000000000111101000000000000000000000000001111111111111111111111111111111111111111111111111111111111111111111111111111111111111111111111111111111111111111111111111111111111111))
	  ((eql first #\b)
	   (setf result #*0000000001000000000000000000000011000000000010100000000000100000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000))
	  ((eql first #\B)
	   (setf result #*1111111110111111111111111111111100111111111101011111111111011111111111111111111111111111111111111111111111111111111111111111111111111111111111111111111111111111111111111111111111111111111111111111111111111111111111111111111111111111111111111111111111111111))
	  ((eql first #\s)
	   (setf result #*0000000001100000000000000000000010000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000))
	  ((eql first #\S)
	   (setf result #*1111111110011111111111111111111101111111111111111111111111111111111111111111111111111111111111111111111111111111111111111111111111111111111111111111111111111111111111111111111111111111111111111111111111111111111111111111111111111111111111111111111111111111))
	  ((and (>= (char-code first) (char-code #\0))
		(<= (char-code first) (char-code #\9)))
	   (if (and (> (length char-string) 2)
		    (and (>= (char-code (char char-string 1)) (char-code #\0))
			 (<= (char-code (char char-string 1)) (char-code #\9))
			 (>= (char-code (char char-string 2)) (char-code #\0))
			 (<= (char-code (char char-string 2)) (char-code #\9))))
	       ;;
	       ;; It is a single character specified in octal
	       ;;
	       (progn 
		 (setf result (do ((x 0 (1+ x))
				   (return 0))
				  ((= x 2) return)
				(setf return (+ (* return 8)
						(- (char-code (char char-string x))
						   (char-code #\0))))))
		 (setf used-length 3))
	     ;;
	     ;; We have a group number replacement.
	     ;;
	     (let ((group (- (char-code first) (char-code #\0))))
	       (setf result `((let ((nstring (subseq string (car (aref *regex-groups* ,group))
						     (cadr (aref *regex-groups* ,group)))))
				(if (< length (+ index (length nstring)))
				    (return-from compare nil))
				(if (not (string= string nstring
						  :start1 index
						  :end1 (+ index (length nstring))))
				    (return-from compare nil)
				  (incf index (length nstring)))))))))
	  (t 
	   (setf result first)))
    (if (and (vectorp result) invert)
	(bit-xor result #*1111111110011111111111111111111101111111111111111111111111111111111111111111111111111111111111111111111111111111111111111111111111111111111111111111111111111111111111111111111111111111111111111111111111111111111111111111111111111111111111111111111111111111 t))
    (values result used-length)))



;;; =======
;;; SCANNER
;;; =======
(defstruct (scanner)
  ;; lex-cats:
  ;; list of lexical categories. a lexical category is represented by
  ;; a tupple of (regexp match-fun category), where regexp is a string
  ;; representing regular expression, match-fun is a pattern matching
  ;; function, and category is any Lisp object which stands for the
  ;; lexical category.
  (lex-cats nil :type list)
  ;; whites:
  ;; structure is similar to lex-cats, but contains the list of
  ;; (regexp match-function).
  ;; regexp is a regular expression which defines a white spaces, and
  ;; match-function is a pattern matcher.
  (whties nil :type list)
  )

;;; DEFLEX
;;;
(defun deflex (scanner regexp cat)
  (let ((pat-matcher (make-regexp-matcher regexp)))
    (cond ((eq cat :white)
	   (let ((old-def (assoc regexp (scanner-whites scanner)
				 :test #'equal)))
	     (if old-def
		 (setf (cdr old-def) (list pat-matcher))
		 (push (list regexp pat-matcher)
		       (scanner-whites scanner)))))
	  (t (let ((old-def (assoc regexp (scanner-lex-cats
					   scanner))))
	       (if old-def
		   (setf (cdr old-def) (list pat-matcher cat))
		   (push (list regexp pat-matcher cat)
			 (scanner-lex-cats scanner)))))
	  )))


;;; ============
;;; TOKEN BUFFER
;;; ============
(defstruct (token-buffer)
  (stream nil :type (or null stream))	; input stream
)


;;; BUILTIN LEXICAL CATEGORIES.
;;;-----------------------------------------------------------------------------

(defmacro declare-bi-token (sym)
  `(setf (get ,sym ':bi-token) t))

;;; WHITE space
(defparameter .white-token. '|WhiteSpace|)

(eval-when (eval load)
  (declare-bi-token .lisp-simple-sexpr.)
  (declare-bi-token .lisp-general-sexpr.)
  (declare-bi-token .String-token.)
  (declare-bi-token .white-token.))


;;;=============================================================================
;;; LOW LEVEL READER
;;;=============================================================================

;;; Syntactic properties of characters:_________________________________________
;;; At the lowest level, each input character has a syntactic property which is 
;;; one of the followings:
;;;  - 'space  : means white space, i.e., normaly the chars chars except
;;;              cr/newline have this property.
;;;  - 'return : cr & newline.
;;;  ** 'white and 'return are always treated as token separators.
;;;  There are some chars which are treated as they stand, i.e., each of which
;;;  construct a token by itself. it is a resposibility of higher procs to treate
;;;  these chars in different ways. In such case, the value of the syntactic
;;;  property is set to a symbol other than 'space, 'return, or 'nil.
;;;  The property 'nil means that a sequnce of these char construct a token.
;;;  The global *reader-read-table* holds the above infos, `!init-read-table'
;;;  sets the property for each chars according to its arguments.
;;;
(declaim (type (integer 0 256) .reader-char-code-limit.))
(defparameter .reader-char-code-limit. 255) 
#-GCL (declaim (type simple-array *reader-read-table*))
#+GCL (declaim (type vector *reader-read-table*))
(defvar *reader-read-table*)
(eval-when (eval load)
  (setf *reader-read-table* (make-array (list .reader-char-code-limit.))))

(defmacro !set-syntax (ch val)
  `(setf (aref *reader-read-table* (the fixnum (char-code ,ch))) ,val))

;;; !INIT-READ-TABLE : List[Char] List[Char] List[Char] -> Void
;;; initialize Chaos read table.
;;;  space  : list of `space' characters
;;;  return : list of `return' characters
;;;  single : list of self terminatig characters
;;;
(defun !init-read-table (space return single)
  (declare (type list space return single)
	   (values t))
  (do ((i 0 (1+ i)))
      ((= i .reader-char-code-limit.))
    (declare (type (integer 0 256) i))
    (setf (aref *reader-read-table* i) nil))
  (dolist (char space)
    (!set-syntax char 'space))
  (dolist (char return)
    (!set-syntax char 'return))
  (dolist (c-c single)
    (!set-syntax (car c-c) (cdr c-c))))

(defmacro reader-get-syntax (ch)
  `(aref *reader-read-table* (the fixnum (char-code ,ch))))

(defmacro reader-valid-char-code (n)
  (once-only (n)
    `(and (<= 0 ,n) (<= ,n .reader-char-code-limit.))))

;;; !SET-SINGLE-READER list-of-chars
;;; make a list of characters be single character symbols (self terminating)
;;; in the reader.
;;; returns list of original status. the return valu can be used for an argument 
;;; of `!set-reader' for recovering the modifications.
;;;
(defun !set-single-reader (l)
  (declare (type list l)
	   (values t))
  (mapcar #'(lambda (x)
	      (declare (type (or simple-string character) x))
	      (let ((chr (if (stringp x)
			     (char (the string x) 0)
			     x)))
		(prog1
		    (cons chr (reader-get-syntax chr))
		  (!set-syntax chr (intern (string x))))))
	  l))

;;; !SET-READER list-of-chars
;;; modify a sequence of characters for syntax as given by associated values.
;;; useful for restoring the old properties of chars modified by !set-single-reader.
;;;
(defun !set-reader (l)
  (declare (type list l)
	   (values t))
  (mapc #'(lambda (x)
	    (declare (type list x))
            (let ((s (car x)))
	      (declare (type (or simple-string character) s))
	      (!set-syntax
	       (if (stringp s)
		   (char (the string s) 0)
		   s)
	       (cdr x))))
	l))


;;; SIMPLE READER_______________________________________________________________
;;;

;;; The eof value.
(eval-when (eval compile load)
  (defparameter *lex-eof* (cons nil nil))
  )

;;; READ-LINES (stream)
;;;
(defconstant newline-string (string #\newline))
(defparameter line-continue-char #\;)

(defparameter .read-line-eof. "")

(defun read-lines (&optional (stream *standard-input*))
  (declare (type stream stream)
	   (values (or list simple-string) fixnum))
  (let (res
	line
	(ll 0)
	l-char 
	(l-total 0))
    (declare (type fixnum l-total ll))
    (loop (setq line (read-line stream nil .read-line-eof.))
	  (when (eq line .read-line-eof.) (return))
	  (when (<= (setq ll (length (the simple-string line))) 0)
	    (return))
	  (incf l-total ll)
	  (decf ll)
	  (setq l-char (char line ll))
	  (if (char= line-continue-char (the character l-char))
	      (progn
		(setq res (concatenate 'string res
				       (setq line (subseq (the simple-string line)
							  0 ll))
				       newline-string))
		;; (decf l-total)
		(when (at-top-level)
		  (princ "> ")
		  (force-output)))
	      (progn
		(setq res (concatenate 'string
				       res
				       (if (char= #\. (the character l-char))
					   (progn
					     (decf l-total)
					     (subseq line 0 ll))
					   line)))
		(return))))
    (if (eq line .read-line-eof.)
	(values *lex-eof* 0)
	(values res l-total))))

;;; the global .reader-ch. holds the last char read.
;;; if the character has a property other than 'nil, the property value is set,
;;; otherwise the character itself is set.
;;;
(defvar .reader-ch. 'space)

;;; the special .escape-char. holds a character which is used as escape
;;; character, i.e., the preceding char is treated as is.
;;;
(declaim (special .escape-char.))
(defvar .default-escape-char. #\\)

;;; 
#-CMU (defconstant control-d #\^D)
#+CMU (defconstant control-d #\)
(defconstant control-d-string "")

(defmacro at-eof () `(eq *lex-eof* .reader-ch.))

(defmacro see-ctrl-d ()
  `(eq .reader-ch. control-d))
  
(defun str-match? (x y)
  (declare (type t x)
	   (type (or symbol simple-string) y)
	   (values (or null t)))
  (and (stringp x)
       (string= (the simple-string x)
		(if (stringp y)
		    (the simple-string y)
		    (string-downcase (string (the symbol y)))))))

(defun lex-string-match(x y)
  (declare (type t x)
	   (type (or atom list) y)
	   (values (or null t)))
  (if (atom y)
      (str-match? x y)
      (member x y :test #'str-match?)))

;;; READER-GET-CHAR : STREAM 
;;; reads a one character from stream, set .reader-ch. handling ESCAPE sequence.
;;;
(declaim (special .reader-escape.))
(defvar .reader-escape. nil)		; flags indicating we are now in `escaped'
					; status.

(defvar .read-buffer. nil)
(defvar .read-pos. 0)
(defparameter eof-char control-d)

(defun reader-get-char (stream)
  (declare (type stream stream)
	   (values t))
  (let ((inch (read-char stream nil *lex-eof*)))
    (cond ((eq inch *lex-eof*)
	   (setf .reader-ch. *lex-eof*))
	  #||
	  (.reader-escape.
	   (setf .reader-ch. inch))
	  ((char= .escape-char. inch)
	   (let ((.reader-escape. t))
	     (setf .reader-ch. 'space)
	     (reader-get-char stream)))
	  ||#
	  (t (let ((val (reader-get-syntax inch)))
	       (setf .reader-ch. (if val val inch)))))))

;;; READ-LEXICON : STREAM -> TOKEN
;;; read a lexicon.
;;;
;;; implementation limit: a lexicon must be of length less than or equal to 256.
;;;
(declaim (type simple-string .reader-buf.))
(defvar .reader-buf. (make-string 256))
(defparameter .chaos-simple-LISP-keyword. "#!")
(defparameter .chaos-general-LISP-keyword. "#!!")

(defun read-lexicon (&optional (stream *standard-input*))
  (declare (type stream stream))
  (let ((p -1)
	res)
    (declare (type fixnum p)
	     (type (or symbol list simple-string) res))
    (setq res
	  (loop (cond ((member .reader-ch. '(#\Rubout #\Backspace))
		       (if (<= 0 p)
			   (decf p 1)))
		      ((characterp .reader-ch.)
		       (incf p)
		       (setf (aref .reader-buf. p) .reader-ch.))
		      (t (let ((c (string .reader-ch.)))
			   (setq .reader-ch. 'space)
			   (return c))))
		(reader-get-char stream)
		(when (at-eof)
		  (if (<= 0 p)
		      (progn (setq .reader-ch. 'space)
			     (return (subseq .reader-buf. 0 (1+ p))))
		      (return *lex-eof*)))
		(when (symbolp .reader-ch.)
		  (return (subseq .reader-buf. 0 (1+ p))))
		))
    ;;
    (lex-consider-token res)
    ))

(defun lex-consider-token (tok)
  (declare (type t tok))
  (if (equal .chaos-simple-LISP-keyword. tok)
      (progn (reader-suppress-ch tok) (list .lisp-simple-sexpr. (read)))
      (if (equal .chaos-general-lisp-keyword. tok)
	  (progn (reader-suppress-ch tok) (list .lisp-general-sexpr. (read)))
	  tok)))

(defun reader-suppress-ch (context &optional (stream *standard-input*))
  (declare (ignore context)
	   (type stream stream)
	   (values t))
  (unless (at-eof)
    (unless (memq .reader-ch. '(space return))
      (unread-char (if (characterp .reader-ch.)
		       .reader-ch.
		       (char (the simple-string (string .reader-ch.)) 0))
		   stream)
      (setq .reader-ch. 'space))))

(defun reader-unread (ch stream)
  (declare (type (or symbol character) ch)
	   (type stream stream)
	   (values t))
  (unless (memq ch '(space return))
    (unread-char (if (characterp ch)
		     ch
		     (char (the simple-string (string (the symbol ch))) 0))
		 stream)
    ch))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

;;; READ-SYM : STREAM -> TOKEN
;;; read characters considered to be constructs of a token, returns
;;; the token recognized.
;;; The followings are treated specially:
;;;  (...)   : read a parenthesized unit. 
;;;  "..."   : read as string constant.
;;;  'c      : read as character constant.
;;;
;;; *reader-input* : token buffer.
;;;
(defvar *reader-input* nil)

;;; *reder-void* is the marker that indicates the buffered token is
;;; consumed, thus we should read a token.
;;;
(defparameter *reader-void* '(void))
(defvar *token-buf* nil)
(defvar *last-token* *reader-void*)

(defun unread-token (&rest ignore)
  (declare (ignore ignore)
	   (values t))
  (unless (eq *last-token* *reader-void*)
    (push *last-token* *token-buf*)
    (setq *last-token* *reader-void*)))

(defun read-sym (&optional (stream *standard-input*) (parse-list nil))
  (declare (type stream stream)
	   (type (or null t) parse-list)
	   (values t))
  (when *token-buf*
    (return-from read-sym (pop *token-buf*)))
  ;; skip white chars.
  (while (memq .reader-ch. '(space return))
    (reader-get-char stream))
  (cond ((at-eof)
	 (setf .reader-ch. 'space)
	 (setq *last-token* *reader-void*)
	 *lex-eof*)
	(t
	 (case .reader-ch.
	   (|(| (if parse-list
		    (setq *last-token* (lex-read-list stream))
		    (progn
		      (setq .reader-ch. 'space)
		      (setq *last-token* "("))))
	   (return (setq *last-token* *reader-void*) nil)
	   (#\"				; string
	    (setq *last-token* (list (lex-read-string stream))))
	   (#\#				; #! or #!!
	    (reader-get-char stream)
	    (cond ((memq .reader-ch. '(space return))
		   (setq *last-token* '("#")))
		  ((eq .reader-ch. *lisp-escape-char*)
		   (setq *last-token* (lex-read-lisp-escape stream)))
		  (t (reader-unread .reader-ch. stream)
		     (setq .reader-ch. #\#)
		     (let ((tok (read-lexicon stream)))
		       (if (equal tok *lex-eof*)
			   (progn (setq *last-token* *reader-void*)
				  *lex-eof*)
			   (setq *last-token* tok))))))
	   ;;
	   (otherwise
	    (if (symbolp .reader-ch.)
		(let ((str (string .reader-ch.)))
		  (setq .reader-ch. 'space)
		  (setq *last-token* (lex-consider-token str)))
		(let ((tok (read-lexicon stream)))
		  (if (eq tok *lex-eof*)
		      (progn (setq *last-token* *reader-void*)
			     *lex-eof*)
		      (setq *last-token* tok)))))))))

;;; builtin string reader
(defun lex-read-string (stream)
  (declare (type stream stream)
	   (values t))
  (reader-unread .reader-ch. stream)
  (let ((str (read stream nil *lex-eof*)))
    (if (eq str *lex-eof*)
	*lex-eof*
	(prog1 
	    (list .String-token. str)
	  (setf .reader-ch. 'space)))))

;; builtin lisp expression
(defun lex-read-lisp-escape (stream)
  (declare (type stream stream)
	   (values list))
  (let ((nx nil))
    (setq nx (reader-get-char stream))
    (while (memq .reader-ch. '(space return))
      (setq nx (reader-get-char stream)))
    (if (eq nx *lisp-escape-char*)
	;; #!!
	(let ((expr (read stream nil *lex-eof*)))
	  (setq .reader-ch. 'space)
	  (if (equal expr *lex-eof*)
	      (progn (setq *last-token* *reader-void*)
		     (setq .reader-ch. 'space)
		     *lex-eof*)
	      (list .lisp-general-sexpr. expr)))
	;; #!
	(let ((expr nil))
	  (setq .reader-ch. 'space)
	  (reader-unread nx stream)
	  (setq expr (read stream nil *lex-eof*))
	  (if (equal expr *lex-eof*)
	      (progn (setq *last-token* *reader-void*)
		     *lex-eof*)
	      (list .lisp-simple-sexpr. expr))))))
    
;;; builtin character reader : obsolate
#||
(defun lex-read-character (stream)
  (let ((char (read-char stream nil *lex-eof*)))
    (if (eq char *lex-eof*)
	*lex-eof*
	(progn
	  (when (eql char #\\)		; escape char
	    (let ((echar (read-char stream nil *lex-eof*)))
	      (if (eq echar *lex-eof*)
		  (return-from lex-read-character *lex-eof*)
		  (setf char
			(case echar
			  (#\n #\Newline)
			  (#\r #\Return)
			  (#\t #\Tab)
			  (#\s #\Space)
			  (#\l #\LineFeed)
			  (#\p #\Page)
			  (otherwise echar))))))
	  (setf .reader-ch. 'space)
	  (list .Char-token. char)))))
||#

;;; read up to matching close parenthesis
;;;
(defun lex-read-list (&optional (stream *standard-input*))
  (declare (type stream stream)
	   (values list))
  (reader-get-char stream)
  (lex-read-rest-of-list stream))

(defun lex-read-rest-of-list (&optional (stream *standard-input*))
  (declare (type stream stream)
	   (values list))
  (while (memq .reader-ch. '(space return))
    (reader-get-char stream))
  (if (at-eof)
      *lex-eof*
      (if (eq '|)| .reader-ch.)
	  (progn
	    (reader-get-char stream)
	    (list "(" ")"))
	  (let ((res (list "("))
		x)
	    (loop (setq x (lex-read stream))
		  (when (eq *lex-eof* x)
		    (return *lex-eof*))
		  (setq res (append res x))
		  ;; (wait-until-non-white stream)
		  (while (memq .reader-ch. '(space return))
		    (reader-get-char stream))
		  (when (eq '|)| .reader-ch.)
		    (reader-get-char stream)
		    (return (nconc res (list ")"))))
		  (when (at-eof)
		    (return *lex-eof*)))
	    ))))

;;; LEX-READ : STREAM -> List[Token]
;;; standard routine to get token from stream.
;;;
(defun bi-token? (tok)
  (declare (type t tok)
	   (values (or null t)))
  (and (consp tok)
       (let ((tm (car tok)))
	 (and (symbolp tm)
	      (get tm ':bi-token)))))

(defun lex-read (&optional (stream *standard-input*))
  (declare (type stream stream)
	   (values t))
  (let ((tok (read-sym stream t)))
    (if (eq *lex-eof* tok)
	*lex-eof*
	(cond ((atom tok)
	       (if tok
		   (list tok)
		   nil))
	      (t (if (bi-token? tok)
		     (list tok)
		     tok))))))

;;; returns t iff the characters in the string are all digit char.

(defmacro all-digit? (string start end)
  (once-only (string)
   ` (the (or null t)
       (do ((s (the fixnum ,start) (1+ s)))
	   ((>= s ,end) t)
	 (declare (type fixnum s end))
	 (if (not (digit-char-p (schar ,string s))) (return nil))))))
    
;;; BUFFERED-INPUT______________________________________________________________
;;; one token is bufferd.

;;; Input Buffering for general reader
;;;   the following routines create a single token buffer, which
;;;   allows look-ahead.
;;;

;;; !LEX-READ-INIT
;;; initialize read table, .escape-char., and .reader-ch..
;;;
(defparameter .default-space-chars.
  '(#\Space #\Tab #\Page #\Linefeed))

(defparameter .default-return-chars.
  '(#\Return #\Newline))

(defparameter .default-single-chars.
  `((#\( . |(|)
    (#\) . |)|)
    (#\, . |,|)
    (#\[ . |[|)
    (#\] . |]|)
    (#\{ . |{|)
    (#\} . |}|)
    ;; (#\! . |!|)
    (,control-d . ,control-d)
    ))

(defun !lex-read-init (&key (space .default-space-chars.)
			    (return .default-return-chars.)
			    (single .default-single-chars.)
			    (escape .default-escape-char.))
  (!init-read-table space return single)
  (setq .escape-char. escape)
  (setq .reader-ch. 'space)
  (setq *reader-input* *reader-void*
	*last-token* *reader-void*
	*token-buf* nil))

;;; !READ-IN
;;; read a token iff the last input is not processed yet,
;;; i.e. *reader-input* == *reader-void*.
;;; the token is set to *reader-input*.
;;;
(defmacro !read-in ()
  ` (when (eq *reader-input* *reader-void*)
      (setq *reader-input* (read-sym))))

(defmacro reader-is-at-eof ()
  `(eq *lex-eof* *reader-input*))

(defmacro at-eof-or-control-d ()
  `(or (reader-is-at-eof)
       (equal *reader-input* control-d-string)))

;;; !READ-DISCARD
;;; discard the last input token.
;;;
(defmacro !read-discard ()
  `(setq *reader-input* *reader-void*))

;;; !READ-SYM
;;; read a token.
;;;
(defun !read-sym ()
  (cond ((eq *reader-input* *reader-void*) (read-sym))
	(t (prog1 *reader-input*
	     (!read-discard)))))

;;;
(defun test-lex (file)
  (!lex-read-init)
  (with-open-file (str file :direction :input)
    (let ((tok nil)
	  (*standard-input* str))
      (while-not (eq tok *lex-eof*)
         (setf tok (!read-sym))
	 (print tok)))))

;;; EOF
