;;;-*- Mode:LISP; Package:TK; Base:10; Syntax:Common-lisp -*-
(in-package "TK")
#|==============================================================================
				 System: CHAOS
			      Module: tools.KERNEL
			     File: show-module.lisp
				  Version: 1.0
					
sawada@sra.co.jp
==============================================================================|#

;;; *NOTE* : This module is GCL specific, uses TCL/TK inteface.

;;; SHOW-SUBMODULE-LIST
;;;
(defun chaos::show-submodule-list (module &optional top-window)
  (let ((subs (chaos::module-submodules module))
	(sub-names nil))
    (unless subs (return-from chaos::show-submodule-list nil))
    (dolist (sub subs)
      (push (with-output-to-string (name)
	      (chaos::print-mod-name (car sub) name))
	    sub-names))
    (setq sub-names (nreverse sub-names))
    ;; make show frame.
    (let ((frame-name (if top-window
			  (conc top-window '.submodule)
			  '.submodule)))
      (unless (winfo :exists frame-name :return 'boolean)
	(frame frame-name :borderwidth 10
	       :bg "gray"
	       :relief "raise")
	(scrollbar (conc frame-name '.scroll)
		   :relief "sunken"
		   :command
		   (tk-conc frame-name ".list yview"))
	(listbox (conc frame-name '.list)
		 :yscroll (tk-conc frame-name ".scroll set")
		 :relief "sunken" :geometry "20x4" :setgrid 1)
	(label (conc frame-name '.label)
	       :text "Submodules"
	       :font :Adobe-times-bold-r-normal-*-80-*
	       :bg "gray"))
      (pack frame-name :side "left")
      (pack (conc frame-name '.label) :side "top")
      (pack (conc frame-name '.list)
	    (conc frame-name '.scroll)
	    :side "left" :fill "y")
      (funcall (conc frame-name '.list) :delete 0 "end")
      (apply (conc frame-name '.list)
	     :insert 0 sub-names))))

;;; SHOW-MOUDLE-BODY module parent-window
;;;
(defun chaos::make-text-title (parent entry-name target)
  (let* ((frame (conc parent '.title))
	 (label (conc frame '.label))
	 (entry (conc frame '.entry))
	 (button (conc frame '.button)))
    (unless (winfo :exists frame :return 'boolean)
      (let ((var-name (intern (format nil
				      "~a-~a-textsearch-string"
				      entry-name
				      (chaos::module-name chaos::*current-module*)))))
	(frame frame)
	(label label :text entry-name :bg "gray" :relief "groove"
	       :bd 4)
	(entry entry :width 20 :relief "sunken" :bd 2
	       :textvariable var-name)
	(bind entry "<Return>" `(TextSearch&Mark ',target ,var-name "search"))
	(button button :text "Find"
		:command `(TextSearch&Mark ',target ,var-name "search")
		:anchor "e")))
    (pack label entry :side "left" :expand "yes" :anchor "w")
    (pack button :side "right")
    frame
    ))

(defun chaos::make-text-window (parent entry-name &optional show-title)
  (let* ((frame (conc parent '|.| entry-name))
	 (title-frame nil)
	 (body-frame (if show-title
			 (conc parent '|.body|)
			 frame))
	 (text (conc body-frame '.text))
	 (scroll (conc body-frame '.scroll)))
    (unless (winfo :exists frame :return 'boolean)
      (frame frame :borderwidth 5))
    (when (and show-title
	       (not (winfo :exists body-frame :return 'boolean)))
      (frame body-frame))
    (unless (winfo :exists scroll :return 'boolean)
      (scrollbar scroll :relief "flat" :command (tk-conc text " yview")))
    (unless (winfo :exists text :return 'boolean)
      (text text
	    :relief "groove"
	    :bd 4
	    :yscrollcommand (tk-conc scroll " set")
	    :width 60
	    :height 10))
    (if show-title
    	(setf title-frame (chaos::make-text-title frame entry-name text)))
    ;;
    (if show-title
	(pack title-frame :side "top" :expand "yes" :fill "x" :anchor "nw"))
    (pack scroll :side "right" :fill "y")
    (pack text :expand "yes" :side "top" :fill "both")
    ;; define styles tags.
    (funcall text :tag :configure 'underline :underline "on")
    (funcall text :tag :configure 'bold :font :Adobe-Courier-Bold-r-Normal-*-100-*)
    (funcall text :tag :configure 'bgstipple :background "black" :borderwidth 0 
	     :bgstipple "gray25")
     (funcall text :tag :configure 'keyword :font :Adobe-Courier-Bold-r-Normal-*-120-*)
     (funcall text :tag :configure 'fgstipple :fgstipple "gray50")
     (if (equal (tk :colormodel text)  "color")
	 (progn 
	   (funcall text :tag :configure 'title :background "#eed5b7")
	   (funcall text :tag :configure 'raised :background "#eed5b7"
		    :relief "raised" 
		    :borderwidth 2)
	   (funcall text :tag :configure 'sunken :background "#eed5b7"
		    :relief "sunken" 
		    :borderwidth 2)
	   (funcall text :tag :configure 'groove :background "#eed5b7"
		    :relief "groove"
		    :borderwidth 2)
	   (funcall text :tag :configure 'search :background "SeaGreen4"
		    :foreground "white")
	   )
	 (progn 
	   (funcall text :tag :configure 'title :background "black" :foreground "white")
	   (funcall text :tag :configure 'raised :background "white" :relief "raised" 
		    :borderwidth 2)
	   (funcall text :tag :configure 'sunken :background "white" :relief "sunken" 
		    :borderwidth 2)
	   (funcall text :tag :configure 'groove :background "white" :relief "groove"
		    :borderwidth 2)
	   (funcall text :tag :configure 'search :background "black"
		    :forground "white")
	   ))
     (if show-title
	 (pack body-frame :expand "yes" :after title-frame :fill "both"))
     (pack frame :expand "yes" :fill "both")
     (values frame text scroll title-frame)))

(defun chaos::create-top-frame-if-need (parent name &optional unique-suffix)
  (let (top
	frame)
    (cond (parent (setf top parent)
		  (setf frame (conc parent name))
		  ;; top frame.
		  (unless (winfo :exists frame :return 'boolean)
		    (frame frame :borderwidth 10)))
	  (t (setf top (conc name (or unique-suffix (gensym))))
	     (unless (winfo :exists top :return 'boolean)
	       (toplevel top))
	     (setf frame (conc top name))
	     (unless (winfo :exists frame :return 'boolean)
	       (frame frame :borderwidth 10))))
    (values top frame)))

;;;-----------------------------------------------------------------------------
;;; -- `display-module' generates implict global variables for binding
;;;     search text strings for signature & axioms declared in the
;;;     module to be displayed.
;;;-----------------------------------------------------------------------------

(defun chaos::display-module (module &optional parent)
  (chaos::with-in-module (module)
    (multiple-value-bind (top-window frame)
	(chaos::create-top-frame-if-need parent
					 '.module
					 (intern
					  (format nil "~a" (chaos::module-name module))))
      (unless parent
	(wm :title top-window (format nil "Module ~a" (chaos::module-name module)))
	(wm :iconname top-window (chaos::module-name module)))
      ;;
      (let (sig-frame
	    ax-frame)
	;; -signature title & body
	(setf sig-frame (chaos::display-signature module frame t))
	;; - axiom 
	(setf ax-frame (chaos::display-axioms module frame t))
	;; main window
	(pack sig-frame :side "top" :expand "yes" :fill "both")
	(pack ax-frame :side "top" :expand "yes" :fill "both")
	(pack frame :expand "yes" :fill "both")
	))))
  
(defun chaos::display-signature (module &optional parent show-title)
  (multiple-value-bind (top-window frame)
      (chaos::create-top-frame-if-need parent
				       '.sig
				       (intern (format nil "~a"
						       (chaos::module-name module))))
    (unless parent
      (wm :title top-window (format nil "Signature of Module ~a"
				    (chaos::module-name module)))
      (wm :iconname top-window (format nil "Sig:~a"
				       (chaos::module-name module))))
    (chaos::with-in-module (module)
      (let ((sorts (chaos::module-sorts module))
	    (op-methods (chaos::module-own-op-methods module))
	    sig-frame
	    sig-text
	    sig-scroll
	    sig-title)
	(multiple-value-setq (sig-frame sig-text sig-scroll sig-title)
	  (chaos::make-text-window frame "Signature" show-title))
	(funcall sig-text :delete 0.0 'end)
	(show-signature sig-text sorts op-methods module)
	(TeXtSearch&Mark sig-text " -> " 'bold t)
	(unless parent
	  (pack frame :expand "yes" :fill "both"))
	frame))))
      
(defun chaos::display-axioms (module &optional parent show-title)
  (multiple-value-bind (top-window frame)
      (chaos::create-top-frame-if-need parent
				       '.axiom
				       (format nil "~a" (chaos::module-name module)))
    (unless parent 
      (wm :title top-window (format nil "Axioms of Module ~a"
				    (chaos::module-name module)))
      (wm :iconname top-window (format nil "Ax:~a"
				       (chaos::module-name))))
    (chaos::with-in-module (module)
      (let ((variables (chaos::module-variables module))
	    (equations (chaos::module-equations module))
	    (rules (chaos::module-rules module))
	    ax-frame
	    ax-text
	    ax-scroll
	    ax-title)
	(multiple-value-setq (ax-frame ax-text ax-scroll ax-title)
	  (chaos::make-text-window frame "Axioms" show-title))
	(funcall ax-text :delete 0.0 'end)
	(show-axioms ax-text variables equations rules module)
	(TextSearch&Mark ax-text " = "  'bold t)
	(TextSearch&Mark ax-text " => " 'bold t)
	(TextSearch&Mark ax-text ":if " 'bold t)
	(unless parent
	  (pack frame :expand "yes" :fill "both"))
	frame))))
    
;;; The utility procedure below searches for all instances of a
;;; given string in a text widget and applies a given tag to each
;;; instance found.
;;; Arguments:
;;;
;;; w -		The window in which to search.  Must be a text widget.
;;; string -	The string to search for.  The search is done using
;;;		exact matching only;  no special characters.
;;; tag -	Tag to apply to each instance of a matching string.
;;;
;;; ** this should be builtin tk command.
;;;
(defun TextSearch&Mark (w string tag &optional (non-delete-previous nil))
  (unless non-delete-previous
    (funcall w :tag :remove tag 0.0 'end))
  (when (or (null string) (string= string ""))
    (return-from TextSearch&Mark nil))
  (let ((mark "mine")
	(m (length string)))
    (funcall w :mark :set mark "0.0")
    (while (funcall w :compare mark '< 'end :return 'boolean)
      (let ((s (funcall w :get mark mark : " + 3000 chars" :return 'string))
	    (n 0) tem)
	(while (setq tem (search string s :start2 n))
	  (funcall w :tag :add tag
		   mark : " + " : tem : " chars"
		   mark : " + " : (setq n (+ tem m)) : " chars"))
	(funcall w :mark :set mark mark : " + " : (- 3000 m) : " chars")))))

;;;
;;;
(defun terpri-window (window &optional (n 1))
  (dotimes (x n)
    (funcall window :insert 'insert "
"
	     )))
(defmacro insertWithTags (window text &rest args)
  `(tk-call "insertWithTags" ,window ,text ,@args))

(Defun show-signature (window sorts op-methods module)
  (let ((chaos::*print-line-limit* 50))
    (insertWithTags window "Sorts:" 'title 'sunken)
    (if sorts
	(progn nil
	       )
	(insertWithTags window " no own sorts" 'bold))
    (terpri-window window 2)
    (insertWithTags window "Operators:" 'title 'sunken)
    (terpri-window window)
    (if op-methods
	(let ((chaos::*print-indent* 2)
	      (text (with-output-to-string (x)
		      (let ((*standard-output* x))
			(dolist (op-meth op-methods)
			  (chaos::print-op-meth2 op-meth module)
			  )
			x))))
	  (insertWithTags window text))
	(insertWithTags window " no own operator declarations" 'bold)
	)))

(defun show-axioms (window variables equations rules module)
  (let ((chaos::*print-line-limit* 50))
    (insertWithTags window "Variables:" 'title 'sunken)
    (if (not variables)
	(insertWithTags window "no variable declaratins" 'bold)
	(let ((txt (with-output-to-string (x)
		     (let ((*standard-output* x))
		       (terpri-window window)
		       (dolist (v (reverse variables))
			 (chaos::print-next)
			 (princ (string (chaos::variable-name (cdr v))))
			 (princ " : ")
			 (chaos::print-sort-name 
			  (chaos::variable-sort (cdr v))
			  chaos::*current-module*))))))
	  (insertWithTags window txt)))
    (terpri-window window 2)
    (insertWithTags window "Equations:" 'title 'sunken)
    (if (not equations)
	(insertWithTags window " no own equations" 'bold)
	(let ((txt (with-output-to-string (x)
		     (let ((*standard-output* x))
		       (terpri-window window)
		       (dolist (e equations)
			 (chaos::print-next)
			 (chaos::print-rule-brief e :no-type))))))
	  (insertWithTags window txt)))
    (terpri-window window 2)
    (insertWithTags window "Rules:" 'title 'sunken)
    (if (not rules)
	(insertWithTags window " no own rules" 'bold)
	(let ((txt (with-output-to-string (x)
		     (let ((*standard-output* x))
		       (terpri-window window)
		       (dolist (e rules)
			 (chaos::print-next)
			 (chaos::print-rule-brief e :no-type))))))
	  (insertWithTags window txt)))))

