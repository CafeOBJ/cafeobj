;;;-*- Mode:LISP; Package:TK; Base:10; Syntax:Common-lisp -*-
;;; $Id: main.lisp,v 1.1.1.1 2003-06-19 08:31:09 sawada Exp $
(in-package "TK")
#|==============================================================================
				 System: CHAOS
					
sawada@sra.co.jp
==============================================================================|#

(defvar chaos::*main-panel-initialized* nil)
(defconstant chaos-top-level-panel '.mainpanel)
(defvar chaos::*no-sort-print-on-tree* nil)
(defvar chaos::*print-term-tree* nil)
;;;
(defun source-rc ()
  (let ((path (truename (pathname "~/.chaos-tk-rc"))))
    (when (probe-file path)
      (with-output-msg ()
	(princ "Loading TCL/TK rc file \~/.chaos-tk-rc...")
	(tk-do "source " :|| (namestring path))
	(princ "done")
	(terpri)))))
;;;
;;;
(defvar *chaos-last-module-name* "")
(defvar *chaos-term-input-window* "")
(defvar *chaos-output-display-window* "")

;;;=============================================================================
;;; MAIN MENU
;;;===============================================================================
(defparameter chaos-top-level-menus
  ' ((file (text "File")
	   (underline 0)
	   (menu (command (label "Load")
			  (command chaos::load-chaos-file)
			  (accelerator "[l]")
			  )
		 (command (label "Edit")
			  (command chaos::edit-file)
			  (accelerator "[e]")
			  )
		 (separator)
		 (command (label "Quit")
			  (command chaos::quit-main-panel)
			  )
		 ))
     (module (text "Module")
	     (underline 0)
	     (menu (command (label "Select")
			    (command chaos::prompt-module-name)
			    (accelerator "[s]")
			    )
		   (separator)
		   (command (label "List Submodules")
			    (command chaos::display-submodule-list))
		   (command (label "List ALL modules")
			    (command chaos::display-module-list)
			    (accelerator "[L]"))
		   (separator)
		   (command (label "Open")
			    )
		   ))
     (desc (text "Show/Describe")
	   (underline 5)
	   (menu (command (label "print current module")
			  (command chaos::show-module-to-display))
		 (command (label "show module in other window")
			  (command chaos::display-module-body)
			  (accelerator "[S]"))
		 (command (label "show current term")
			  (command chaos::display-current-term))
		 (command (label "show rules")
			  (command chaos::show-rules-to-display))
		 (separator)
		 (command (label "describe module")
			  (command chaos::describe-module-to-display))
		 (command (label "describe operator")
			  (command chaos::describe-operator-to-display))))
      (tstat (text "Switches")
	   (underline 0)
	   (menu (checkbutton (label "trace rewrite")
			      (variable (boolean chaos::$$trace-rewrite)))
		 (checkbutton (label "trace whole")
			      (variable (boolean chaos::$trace-whole)))
		 (checkbutton (label "reduce on demand")
			      (variable (boolean chaos::*perform-on-demand-reduction*)))
		 (checkbutton (label "reduce builtins eagerly")
			      (variable (boolean chaos::*reduce-builtin-eager*)))
		 (separator)
		 (checkbutton (label "verbose")
			      (variable (boolean chaos::*chaos-verbose*)))
		 (checkbutton (label "display tree")
			      (variable (boolean chaos::*print-term-tree*)))
		 (checkbutton (label "no sort in term tree")
			      (variable (boolean chaos::*no-sort-print-on-tree*)))
		 (separator)
		 (checkbutton (label "include bool")
			      (variable (boolean chaos::*include-bool*)))
		 ))
    ))


;;;===============================================================================
;;; Toplevel panel
;;;===============================================================================
(defvar *chaos-windows-so-far* nil)

(defun chaos::init-main-panel ()
  (unless chaos::*main-panel-initialized*
    ;; we don't use root window |.|
    (wm :withdraw '|.|)
    ;; create top panel
    (if (winfo :exists chaos-top-level-panel :return 'boolean)
	(destroy chaos-top-level-panel))
    (let* ((top (toplevel chaos-top-level-panel))
	   (menu-frame (conc top '.menu))
	   (cont-frame (conc top '.control)))
      ;;
      (wm :title chaos-top-level-panel "Chaos Toplevel")
      (wm :iconname chaos-top-level-panel "Chaos:Toplevel")
      ;; menu
      (chaos::make-menus menu-frame chaos-top-level-menus)
      ;; control frame
      (let ((c-mod-label (conc top '.cmod-label))
	    (c-mod-entry (conc top '.cmod-entry))
	    (parse-button (conc top '.parse))
	    (red-button (conc top '.reduce)))
	(frame cont-frame :bd 2 :relief "groove")
	(button parse-button
		:text "Parse"
		:font :Adobe-helvetica-Bold-r-normal--12-*
		:command 'chaos::parse-displayed-term)
	(button red-button
		:text "Reduce"
		:font :Adobe-helvetica-Bold-r-normal--12-*
		:command 'chaos::reduce-displayed-term)
	(label c-mod-label :text "Current module:"
	       :font :Adobe-helvetica-medium-r-normal--12-*)
	(entry c-mod-entry :relief "sunken" :width 40
	       :font :Adobe-helvetica-medium-r-normal--12-*
	       :textvariable '*chaos-last-module-name*)
	(tk-do "chaos:eb:emacs_init " :|| c-mod-entry)
	(bind c-mod-entry "<Return>" 'chaos::select-current-module)
	(pack parse-button red-button
	      c-mod-label c-mod-entry :side "left" :in cont-frame
	      :padx 2)
	;; term input frame
	(multiple-value-bind (t-frame term-text)
	    (chaos::tk-make-text-window :parent top
					:entry-name "termInput"
					:show-title 1
					:height 4)
	  (setf *chaos-term-input-window* term-text)
	  (tk-do "chaos:tb:emacs_init " :|| term-text)
	  (let ((frame (intern term-text)))
	    (setf (symbol-function frame)
		  (make-widget-instance frame 'text))
	    (bind frame "<Tab>" (tk-conc term-text " insert insert {    }"))
	    (bind frame "<Double-Button-1>" 'chaos::reduce-displayed-term)
	    (bind frame "<Double-Button-3>" 'chaos::parse-displayed-term))
	  ;; output display area
	  (multiple-value-bind (text-frame d-text)
	      (chaos::tk-make-text-window :parent top
					  :width 68
					  :height 24
					  :background 'white
					  :font "-*-fixed-medium-r-*--13-*"
					  :relief "groove"
					  :entry-name "workingSheet")
	    ;; we must use fixed font for output window.
	    (setf *chaos-output-display-window* d-text)
	    ;; (tk::tk-do *chaos-output-display-window* :||
	    ;;  " configure -font -*-fixed-medium-r-*--13-*")
	    ;; add a tag 
	    (tk::tk-do *chaos-output-display-window* :||
		       " tag configure bold -font -Adobe-Helvetica-Bold-R-Normal--12-*")
	    (tk::tk-do *chaos-output-display-window* :||
		       " tag configure title -font -Adobe-Helvetica-Bold-R-Normal--14-* -relief sunken")
	    (tk::tk-do *chaos-output-display-window* :||
		       " tag configure titlecaphead -font -Adobe-new*-medium-i-normal-*-40-* -relief groove")
	    (tk::tk-do *chaos-output-display-window* :||
		       " tag configure titlelowers -font -Adobe-new*-medium-i-normal-*-24-* -foreground darkseagreen4")
	    (tk::tk-do *chaos-output-display-window* :||
 " tag configure titlecomment -font -*-courier-bold-r-normal-*-12-* -foreground darkseagreen4")
	    ;; (tk-do d-text : " configure -font -*-fixed-medium-r-normal--14-*")
	    (tk-do "chaos:tb:emacs_init " :|| d-text)
	    ;;
	    (let (find-panel
		  (clear-button (conc top '.clear)))
	      (setf find-panel
		    (tk-do "chaos:make-find-panel " :|| top :|| " {" d-text "}"))
	      (button clear-button :text "Clear Output"
		      :font :Adobe-helvetica-bold-r-normal--12-*
		      :relief "sunken"
		      :command 'chaos::display-title)
	      (pack clear-button :in find-panel :side "right" :padx 10)
	      (pack find-panel :side "bottom" :expand "yes" :fill "x")
	      )
	    ;; set chaos defaults values
 	    (setk chaos::*include-bool* t)
	    (setf chaos::*running-with-tk* t)
	    (setk chaos::*reduce-builtin-eager* t)
	    ;;
	    ;;
	    (pack cont-frame :side "top" :anchor "ne" :expand "yes" :fill "both")
	    (pack t-frame :side "top" :after cont-frame :expand "yes" :fill "both")
	    (pack text-frame :side "top" :after t-frame :expand "yes" :fill "both")
	    ;; 
	    (setf *chaos-windows-so-far* nil)
	    ))))))
      
(defun chaos::display-title ()
  (tk-do *chaos-output-display-window* :|| " delete 0.0 end")
  ;;(tk-do "chaos:tagged_insert " :|| *chaos-output-display-window*
  ;;: " {C} titlecaphead")
  (tk-do "chaos:tagged_insert " :|| *chaos-output-display-window*
	 :|| " {Chaos : } {titlelowers}")
  (tk-do "chaos:tagged_insert " :|| *chaos-output-display-window*
	 " { with CafeOBJ syntax version 0.8a - Feb 1996 -} {titlecomment}")
  )

(defun chaos::quit-main-panel ()
  (when (chaos::tk-confirm :text "Are you surely want to QUIT?")
    (setf chaos::*running-with-tk* nil)
    (destroy chaos-top-level-panel)
    (dolist (w *chaos-windows-so-far*)
      (if (winfo :exists w :return 'boolean)
	  (destroy w)))))

(defun chaos::start-ui ()
  (tkconnect)
  (chaos::init-main-panel)
  (chaos::tk-dialog chaos-top-level-panel)
  (chaos::display-title))

;;;-------------------------------------------------------------------------------
;;; UTILS
;;;===============================================================================
(defun chaos::display-string-to-window (string &optional tag)
  (when (and string (not (string= string "")))
    (tk-do "chaos:tkb:eof " :|| *chaos-output-display-window* :|| " dummy " :|| "dymmy")
    (chaos::terpri-window *chaos-output-display-window*)
    (if tag
	(case tag
	  (:bold (tk-do "chaos:tagged_insert " :|| *chaos-output-display-window*
			:|| " {" :|| string :|| " } bold"))
	  (:title (tk-do "chaos:tagged_insert " :|| *chaos-output-display-window*
			 :|| " {" :|| string :|| " } title"))
	  (:underline
	   (tk-do "chaos:tagged_insert " :|| *chaos-output-display-window*
		  :|| " {" :|| string :|| " } underline"))
	  (:search
	   (tk-do "chaos:tagged_insert " :|| *chaos-output-display-window*
		  :|| " {" :|| string :|| " } search"))
	  (t (warn "option ~s is not supported" tag)))
	(tk-do "chaos:tagged_insert " :|| *chaos-output-display-window*
	       :|| " {" :|| string :|| " }"))))

(defun chaos-eval-mod (toks)
  (let ((val (chaos::eval-modexp toks)))
    (if (chaos::modexp-is-error val)
	(progn
	  (chaos::with-output-chaos-warning ()
	    (format t "No such module ~a" toks))
	  nil)
	(progn
	  (setq chaos::*last-module* val)
	  val))))

(defun chaos::get-string-from-selection ()
  (if (chaos::tk-no-selection)
      nil
      (tk-do "selection get")))

(defun chaos::get-term-input-text-if-any ()
  (tk-do "chaos:get:term " :|| *chaos-term-input-window*))

(defun chaos::set-current-module-name (module)
  (setk *chaos-last-module-name*
	(with-output-to-string (s)
	  (let ((*standard-output* s))
	    (chaos::print-mod-name module)
	    s))))

;;;===============================================================================
;;; TOPLEVEL Command processors
;;;===============================================================================

;;;
;;; Setting current modules
;;;-------------------------------------------------------------------------------
(defun chaos::prompt-module-name ()
  (let ((mod-name (chaos::tk-prompt :text "enter a module name:"
				    :title "select module"))
	(old *chaos-last-module-name*))
    (unless (string= mod-name "")
      (if (chaos-eval-mod (list mod-name))
	  (setk *chaos-last-module-name* mod-name)
	  (setk *chaos-last-module-name* old)))))
    
(defun chaos::select-current-module ()
  (unless (string= *chaos-last-module-name* "")
    (unless (chaos-eval-mod (list *chaos-last-module-name*))
      (setk *chaos-last-module-name*
	    (with-output-to-string (s)
	      (let ((*standard-output* s))
		(chaos::print-mod-name chaos::*last-module*)
		s))))))


;;; Load Chaos file
;;;-------------------------------------------------------------------------------
(defun chaos::load-chaos-file ()
  (let ((file-path (chaos::tk-select-file-name)))
    (if file-path
	(chaos::cafeobj-input (namestring file-path))))) 

;;; Edit File
;;;-------------------------------------------------------------------------------
(defun chaos::edit-file ()
  (let ((file-path (chaos::tk-select-file-name t)))
    (if file-path
	(tk-do "chaos:edit-file " :|| (namestring file-path)))))


;;;
;;; PARSE
;;;-------------------------------------------------------------------------------
(defun chaos::parse-displayed-term ()
  (let ((text (chaos::get-term-input-text-if-any)))
    (when (string= text "")
      (chaos::tk-alert :title "Chaos Warinig"
		       :text "No term in termInput window")
      (return-from chaos::parse-displayed-term nil))
    (if chaos::*last-module*
	(chaos::with-in-module (chaos::*last-module*)
	  (let ((res (chaos::simple-parse-from-string text))
		(chaos::*print-line-limit* 54)
		(chaos::*print-indent* (+ 2 chaos::*print-indent*)))
	    (setq chaos::$$term res)
	    (let* ((chaos::*fancy-print* t)
		   (tm (with-output-to-string (res)
			 (let ((*standard-output* res))
			   (chaos::term-print chaos::$$term *standard-output* nil)
			   (princ " :|| ")
			   (chaos::print-check)
			   (chaos::print-sort-name
			    (chaos::term-sort chaos::$$term)
			    chaos::*current-module*)
			   (terpri))))
		   (tree (if chaos::*print-term-tree*
			     (with-output-to-string (res)
			       (let ((*standard-output* res))
				 (chaos::print-term-tree
				  chaos::$$term
				  (not chaos::*no-sort-print-on-tree*))
				 res))
			     nil)))
	      (chaos::display-string-to-window "Parse:" :title)
	      ;; (chaos::display-string-to-window tm :bold)
	      (chaos::display-string-to-window tm)
	      (when tree (chaos::display-string-to-window tree))
	      )))
	(chaos::with-output-chaos-error ()
	  (chaos::tk-alert :title "Chaos Warning"
			   :text "No current module!")))))
    
;;;
;;; SHOW TERM
;;;-------------------------------------------------------------------------------
(defun chaos::display-current-term ()
  (if (and chaos::$$term (not (eq 'chaos::void chaos::$$term)))
      (chaos::with-in-module (chaos::*last-module*)
	(let ((chaos::*print-line-limit* 54)
	      (chaos::*print-indent* (+ 2 chaos::*print-indent*)))
	  (let* ((chaos::*fancy-print* t)
		 (tm (with-output-to-string (res)
		       (let ((*standard-output* res))
			 (chaos::term-print chaos::$$term *standard-output* nil)
			 (princ " : ")
			 (chaos::print-check)
			 (chaos::print-sort-name
			  (chaos::term-sort chaos::$$term)
			  chaos::*current-module*)
			 (terpri))))
		 (tree (if chaos::*print-term-tree*
			   (with-output-to-string (res)
			     (let ((*standard-output* res))
			       (chaos::print-term-tree
				chaos::$$term
				(not chaos::*no-sort-print-on-tree*))
			       res))
			   nil)))
	    (chaos::display-string-to-window "Current term:" :title)
	    ;; (chaos::display-string-to-window tm :bold)
	    (chaos::display-string-to-window tm)
	    (chaos::display-string-to-window tree)
	    )))
      (chaos::tk-alert :text "No current term")))

;;;
;;; REDUCE
;;;-------------------------------------------------------------------------------
(defun chaos::reduce-displayed-term ()
  (let ((text (chaos::get-term-input-text-if-any)))
    (unless text
      (chaos::tk-alert :title "Chaos Warinig"
		       :text "No selection in termInput window"))
    (if chaos::*last-module*
	(chaos::with-in-module (chaos::*last-module*)
	  (setf text (chaos::read-term-from-string text))
	  (multiple-value-bind (res stat)
	      (chaos::eval-ast (chaos::%reduce text nil t))
	    (chaos::display-string-to-window "Rewrite:" :title)
	    (chaos::display-string-to-window res :bold)
	    (chaos::display-string-to-window stat))))))

;;;
;;; MODULE LIST, SUBMODULE LIST
;;;-------------------------------------------------------------------------------
(defun chaos::display-module-list ()
  (let (update-button )
    (setf update-button
	  (tk-do
	   "chaos:MakeModuleListPanel -title {Module List} -width 20 -height 16 -id .modulelist"))
    (setf (symbol-function '.modulelist.modules)
	  (make-widget-instance '.modulelist.modules 'listbox))
    (bind '.modulelist.modules "<Double-Button-1>"
	  'chaos::choose-module-from-module-list)
    (bind '.modulelist.modules "<Double-Button-3>"
	  'chaos::show-module-from-module-list)
    (let ((up-fun (intern update-button)))
      (setf (symbol-function up-fun)
	    (make-widget-instance up-fun 'button))
      (funcall up-fun :configure
	       :command 'chaos::update-module-list-all))
    (pushnew '.modulelist *chaos-windows-so-far*)
    (chaos::update-module-list-all)
    ))

(defun chaos::update-module-list-all ()
  (let ((modules nil))
    (maphash #'(lambda (key mod)
		 (declare (ignore key))
		 (push mod modules))
	     chaos::*modules-so-far-table*)
    (chaos::update-module-list '.modulelist.modules modules)))

(defun chaos::update-module-list (window modules)
  (if (winfo :exists window :return 'boolean)
      (progn
	(funcall window :delete 0 'end)
	(setf modules (sort (mapcar #'(lambda (mod)
					(with-output-to-string (str)
					  (chaos::print-mod-name mod str)
					  str))
				    modules)
			    #'string<))
	(dolist (m modules)
	  (tk-do window :|| " insert end " :|| m)))
      (chaos::tk-alert :text
		       (format nil "Panic! module list window ~a vanished!!"
			       window))))

(defun chaos::display-submodule-list ()
  (unless chaos::*last-module*
    (chaos::tk-alert :text "No current module!")
    (return-from chaos::display-submodule-list nil))
  (let* ((w-id (intern (tk-conc "." *chaos-last-module-name* "SUBS")))
	 (list-box (conc w-id '.modules)))
    (let ((the-module chaos::*last-module*)
	  update-button)
      (setf update-button
	    (tk-do "chaos:MakeModuleListPanel -title "
		   :|| (format nil "{~a:Submodules}" *chaos-last-module-name*)
		   :|| " -iconname "
		   :|| (format nil "{~a:Submodules}" *chaos-last-module-name*)
		   :|| " -id " w-id
		   :|| " -width 20 -height 5 "
		   :|| " -message "
		   :|| (format nil "{Submodules of ~a}"
			     *chaos-last-module-name*)))
      (setf (symbol-function list-box)
	    (make-widget-instance list-box 'listbox))
      (bind list-box "<Double-Button-1>"
	    'chaos::choose-module-from-module-list)
      (bind list-box "<Double-Button-3>"
	    'chaos::show-module-from-module-list)
      (let ((up (intern update-button)))
	(setf (symbol-function up)
	      (make-widget-instance up 'button))
	(funcall up :configure
		 :command #'(lambda ()
			      (chaos::update-module-list
			       list-box
			       (mapcar #'(lambda (x) (car x))
				       (chaos::module-submodules the-module))))))
      (pushnew w-id *chaos-windows-so-far*)
      (chaos::update-module-list list-box
				 (mapcar #'(lambda (x) (car x))
					 (chaos::module-submodules
					  chaos::*last-module*))))))
	 
(defun chaos::choose-module-from-module-list ()
  (let ((mod-name (chaos::get-string-from-selection)))
    (if mod-name
	(if (chaos-eval-mod (list mod-name))
	    (setk *chaos-last-module-name* mod-name))
	)))

(defun chaos::show-module-from-module-list ()
  (let ((mod-name (chaos::get-string-from-selection)))
    (if mod-name
	(let ((val (chaos::modexp-top-level-eval (list mod-name))))
	  (if (chaos::modexp-is-error val)
	      (progn
		(chaos::with-output-chaos-warning ()
		  (format t "Could not find the module ~a, sorry" mod-name))
		nil)
	      (chaos::display-module val)))
	(chaos::tk-alert :text "No selection in module list"))))
      

;;; DISPLAY-MODULE-BODY
;;;-------------------------------------------------------------------------------
(defun chaos::display-module-body ()
  (if chaos::*last-module*
      (chaos::display-module chaos::*last-module*)
      (chaos::tk-alert :text "No current module")))

;;; DISPLAY-MODULE module &optional parent-widget
;;; -- `display-module' generates implict global variables for binding
;;;     search text strings for signature & axioms declared in the
;;;     module to be displayed.
;;;-----------------------------------------------------------------------------
(defun chaos::display-module (module &optional parent)
  (chaos::with-in-module (module)
    (multiple-value-bind (top-window frame)
	;; `module-name' should be corrected : TODO
	(chaos::create-top-frame-if-need parent
					 '.module
					 (intern
					  (format nil "~a" (chaos::module-name module))))
      (unless parent
	(wm :title top-window (format nil "Module ~a" (chaos::module-name module)))
	(wm :iconname top-window (chaos::module-name module)))
      ;;
      (let (sig-frame
	    sig-text
	    ax-frame
	    ax-text
	    find-panel
	    (hide (conc top-window '.hide)))
	;;
	(funcall frame :configure :background 'seashell2)
	;; -signature title & body
	(multiple-value-setq (sig-frame sig-text)
	  (chaos::display-signature module frame t))
	(tk-do sig-frame :|| " configure -bd 2 -relief groov -background seashell2")
	;; - axiom 
	(multiple-value-setq (ax-frame ax-text)
	  (chaos::display-axioms module frame t))
	(tk-do ax-frame :|| " configure -bd 2 -relief groov -background seashell2")
	;; - find panel
	(setf find-panel (tk-do "chaos:make-find-panel " frame
				" { " sig-text
				1space-string ax-text " }"))
	;; main window
	(pack find-panel :side "top" :anchor "e")
	(pack sig-frame ax-frame :side "top"
	      :expand "yes" :fill "both")
	;; hide button
	(unless (or parent (winfo :exists hide :return 'boolean))
	  (button hide :text "Hide" :command (tk-conc "destroy " top-window)
		  :font :adobe-courier-bold-r-normal--*-100-*))
	(unless parent
	  (pack hide :side "bottom" :anchor "se" :in frame))
	(pack frame :expand "yes" :fill "both")
	;;
	(pushnew top-window *chaos-windows-so-far*)
	))))
  
;;; DISPLAY-SIGNATURE
;;;
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
	  (chaos::tk-make-text-window :parent frame
				      :entry-name "Signature"
				      :background 'white
				      :frameback 'seashell2
				      :show-title show-title))
	(tk-do sig-text :|| " delete 0.0 end")
	(chaos::show-signature-to-window sig-text sorts op-methods module)
	(chaos::tk-TeXt-Search&Mark sig-text " -> " 'keyword nil)
	(let ((text (intern sig-text)))
	  (setf (symbol-function text)
		(make-widget-instance text 'text))
	  (funcall text :configure :state "disabled"))
	(pack sig-frame :expand "yes" :fill "both")
	(unless parent
	  (pack frame :expand "yes" :fill "both"))
	(values frame sig-text)))))
      
;;; DISPLAY-AXIOMS
;;;
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
	  (chaos::tk-make-text-window :parent frame
				      :background 'grey90
				      :entry-name "Axioms"
				      :frameback 'seashell2
				      :show-title show-title))
	(tk-do ax-text :|| " delete 0.0 end")
	(chaos::show-axioms-to-window ax-text variables equations rules module)
	(chaos::tk-Text-Search&Mark ax-text " = "  'keyword nil)
	(chaos::tk-Text-Search&Mark ax-text " => " 'keyword nil)
	(chaos::tk-Text-Search&Mark ax-text ":if " 'keyword nil)
	(let ((text (intern ax-text)))
	  (setf (symbol-function text)
		(make-widget-instance text 'text))
	  (funcall text :configure :state "disabled"))
	(pack ax-frame :expand "yes" :fill "both")
	(unless parent
	  (pack frame :expand "yes" :fill "both"))
	(values frame ax-text)))))
    
(defun chaos::show-signature-to-window (window sorts op-methods module)
  (let ((chaos::*print-line-limit* 60))
    (tk-do "insertWithTags " :|| window " {Sorts:} " :|| " title sunken")
    (if sorts
	(let ((text (with-output-to-string (x)
		      (let ((*standard-output* x))
			(mapc #'(lambda (s)
				  (chaos::print-sort-name2 s
							   chaos::*current-module*))
			      sorts)
			x))))
	  (chaos::terpri-window window)
	  (tk-do "insertWithTags " :|| window :|| " {" :|| text "}"))
	(tk-do "insertWithTags " :|| window :|| " { no own sorts}" :|| " bold"))
    (chaos::terpri-window window 2)
    (tk-do "insertWithTags " :|| window " {Operators:} " :|| " title sunken")
    (chaos::terpri-window window)
    (if op-methods
	(let ((chaos::*print-indent* 2)
	      (text (with-output-to-string (x)
		      (let ((*standard-output* x))
			(dolist (op-meth op-methods)
			  (chaos::print-op-meth2 op-meth module)
			  )
			x))))
	  (tk-do "insertWithTags " :|| window :|| " {" :|| text "}"))
	(tk-do "insertWithTags " :|| window " { no own operator declarations}" :|| " bold")
	)))

(defun chaos::show-axioms-to-window (window variables equations rules module)
  (let ((chaos::*print-line-limit* 60))
    (tk-do "insertWithTags " :|| window :|| " {Variables:}" :|| " title sunken")
    (if (not variables)
	(tk-do "insertWithTags " :|| window " { no variable declarations}" :|| " bold")
	(let ((txt (with-output-to-string (x)
		     (let ((*standard-output* x))
		       (chaos::terpri-window window)
		       (dolist (v (reverse variables))
			 (chaos::print-next)
			 (princ (string (chaos::variable-name (cdr v))))
			 (princ " :|| ")
			 (chaos::print-sort-name 
			  (chaos::variable-sort (cdr v))
			  chaos::*current-module*))))))
	  (tk-do "insertWithTags " :|| window :|| " {" :|| txt "}")))
    (chaos::terpri-window window 2)
    (tk-do "insertWithTags " :|| window :|| " {Equations:}" :|| " title sunken")
    (if (not equations)
	(tk-do "insertWithTags " :|| window :|| " { no own equations}" :|| " bold")
	(let ((txt (with-output-to-string (x)
		     (let ((*standard-output* x))
		       (chaos::terpri-window window)
		       (dolist (e equations)
			 (chaos::print-next)
			 (chaos::print-rule-brief e :no-type))))))
	  (tk-do "insertWithTags " :|| window :|| " {" :|| txt "}")))
    (chaos::terpri-window window 2)
    (tk-do "insertWithTags " :|| window  " {Rules:}" :|| " title sunken")
    (if (not rules)
	(tk-do "insertWithTags " :|| window :|| " { no own rules}" :|| " bold")
	(let ((txt (with-output-to-string (x)
		     (let ((*standard-output* x))
		       (chaos::terpri-window window)
		       (dolist (e rules)
			 (chaos::print-next)
			 (chaos::print-rule-brief e :no-type))))))
	  (tk-do "insertWithTags " :|| window :|| " {" txt "}")))))

;;; PRINTING INFOS
;;;-------------------------------------------------------------------------------

;;; SHOW MDOULE
;;;
(defun chaos::show-module-to-display ()
  (let ((chaos::*print-line-limit* 60))
    (unless chaos::*last-module*
      (chaos::tk-alerm :title "No current"
		       :text "No current module")
      (return-from chaos::show-module-to-display nil))
    (let ((res (with-output-to-string (s)
		 (let ((*standard-output* s))
		   (chaos::show-module chaos::*last-module*))
		 s)))
      (chaos::display-string-to-window
       (format nil "Module ~a:" *chaos-last-module-name*) :title)
      (chaos::display-string-to-window res))))

;;;
;;; SHOW RULES
;;;
(defun chaos::show-rules-to-display ()
  (let ((chaos::*print-line-limit* 60))
    (unless chaos::*last-module*
      (chaos::tk-alerm :title "No current"
		       :text "No current module")
      (return-from chaos::show-rules-to-display nil))
    (let ((res (with-output-to-string (s)
		 (let ((*standard-output* s))
		   (chaos::print-module-rules chaos::*last-module*))
		 s)))
      (chaos::display-string-to-window
       (format nil "Rewrite rules of Module ~a" *chaos-last-module-name*)
       :title)
      (chaos::display-string-to-window res))))

;;;
;;; DESCRIBE MODULE
;;; 
(defun chaos::describe-module-to-display ()
  (let ((chaos::*print-line-limit* 50))
    (unless chaos::*last-module*
      (chaos::tk-alerm :title "No current"
		       :text "No current module")
      (return-from chaos::describe-module-to-display nil))
    (let ((res (with-output-to-string (s)
		 (let ((*standard-output* s))
		   (chaos::describe-module chaos::*last-module*))
		 s)))
      (chaos::display-string-to-window
       (format nil "Brief description of module ~a"
	       *chaos-last-module-name*) :title)
      (chaos::display-string-to-window res))))

;;;
;;; DESCRIBE OPERATOR
;;;
(defun chaos::describe-operator-to-display ()
  (let ((chaos::*print-line-limit* 60)
	op-name)
    (unless chaos::*last-module*
      (chaos::tk-alerm :title "No current"
		       :text "No current module")
      (return-from chaos::describe-operator-to-display nil))
    (chaos::with-in-module (chaos::*last-module*)
      (let ((res (with-output-to-string (s)
		   (let ((*standard-output* s)
			 ops)
		     (setf op-name (chaos::tk-prompt :title "Operator?"
						     :text "Input operator name:"))
		     (when (string= op-name "")
		       (return-from chaos::describe-operator-to-display nil))
		     (chaos::show-op (chaos::read-modexp-from-string op-name) t)))))
	(chaos::display-string-to-window
	 (format nil "Details of operator ~a" op-name) :title)
	(chaos::display-string-to-window res)))))

