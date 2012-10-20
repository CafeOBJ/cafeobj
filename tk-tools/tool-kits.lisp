;;;-*- Mode:LISP; Package:TK; Base:10; Syntax:Common-lisp -*-
(in-package "TK")
#|==============================================================================
				 System: CHAOS
			      Module: tools.KERNEL
			       File: tool-kits.lisp
				  Version: 1.0
					
sawada@sra.co.jp
==============================================================================|#

;;;!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!
;;;CAUTION this file requires `tcl' has been loaded BEFORE eval, load, compile
;;;!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!
(defconstant 1space-string " ")

(defun chaos::call-tkproc (proc-name result-type arglist)
  (declare (type string proc-name)
	   (type list arglist))
  (with-tk-command
      (pp proc-name :no-quotes-and-no-leading-space)
    (print-arglist tk-command arglist)
    (call-with-result-type tk-command result-type)))

(defmacro chaos::define-tk-function (fun-name tcl-proc &optional (result-type 'string))
  ` (progn
      (setf (symbol-function ',fun-name)
	    #'(lambda (&rest l)
		(block funname
		  (chaos::call-tkproc ,tcl-proc ',result-type l))))))


;;; TK-SOURCE file-name
;;;
(chaos::define-tk-function chaos::tk-source "source")

;;; TK-CD
;;;
(chaos::define-tk-function chaos::tk-cd "cd")

;;; TK-PWD
(chaos::define-tk-function chaos::tk-pwd "pwd")

;;; TK-NEW-TOP prefix args
;;; creates a new toplevel, avoiding name conflics
;;;
(chaos::define-tk-function chaos::tk-new-top "chaos:new_toplevel" t)

;;; TK-SLECTION-IF-ANY
;;; returns selection if it exists, else ""
;;;
(chaos::define-tk-function chaos::tk-selection-if-any "chaos:selection_if_any")

;;; TK-BEEP w visible
;;; ring bell in widget w
;;; visible sould be 1 : use visible bell
;;;               or 0 : non visible
;;;
(chaos::define-tk-function chaos::tk-beep "chaos:beep" boolean)

;;; TK-NO-SELECTION
;;; return true if there is no selection.
;;; 
(chaos::define-tk-function chaos::tk-no-selection "chaos:no_selection" boolean)

;;; TK-DEFAULT-BUTTON button widget...
;;; bind <Return> to default button. widget... is one or more widgets that
;;; can have the keyboard focus.
;;;
(chaos::define-tk-function chaos::tk-default-button "chaos:default_button")

;;; TK-CANCEL-BUTTON button widget...
;;; set up binding for cancel button.
;;; widget.. is one or more widgets that can have the keyboard fucus.
;;; the following bindings are made:
;;;  <Control-c> : invoke
;;;  <Control-g> : invoke
;;;  <Meta-q>    : invoke
;;;  <Meta-period> : invoke
;;;
(chaos::define-tk-function chaos::tk-cancel-button "chaos:cancel_button")

;;; TK-TAB-RING widget ...
;;; bind Tab and Shift-Tab to cycle through widgets.
;;; widget.. is the list of widgets to bind, in order.
;;;
(chaos::define-tk-function chaos::tk-tab-ring "chaos:tab_ring")

;;; TK-DIALOG w
;;; arrang to position window w near center of screen.
;;;
(defun chaos::tk-dialog (w)
  (tk-do "chaos:dialog " :|| w :|| " 1"))

;;; TK-RULE parent &rest args
;;; return a rule suitable for parent.
;;; used as argument to a pack command.
;;;
(chaos::define-tk-function chaos::tk-rule "chaos:rule" t)

;;; TK-FILLER parent &rest args
;;; returns a filler frame suitable for parent.
;;; used as argument to a pack command.
;;;
(chaos::define-tk-function chaos::tk-filler "chaos:filler" t)

;;; TK-CONFIGURE-FONT widget &rest fontlist
;;; use font from list, or default tries to set widget's font to each font in list.
;;; if a font is 'default', trues to se to X defult font.
;;; if a font "", sets to courie 12-point.
;;;
(chaos::define-tk-function chaos::tk-cofigure-font "chaos:configure_font")

;;; TK-CONFIGURE-TAG-FONT widget tag fontlist
;;; use font from list, or defult ties to set tag's font to each font in list.
;;; if a font is 'default', tries to se to X default font.
;;; if a font is "", sets to oourier 12-point.
;;;
(chaos::define-tk-function chaos::tk-configure-tag-font "chaos:configure_tag_font")

;;; TK-CONFIRM options...
;;; creates Cancel/OK dialog box and returns the answer.
;;; options include
;;;   :title (default "Confirm")
;;;   :text (default "Are you sure?")
;;;   :yesbutton (default "OK")
;;;   :nobutton (default "Cancel")
;;; returns true on OK, nil on Cancel
;;;
(chaos::define-tk-function chaos::tk-confirm "chaos:confirm" boolean)

;;; TK-ALERT options...
;;; show alert box. wait until users confirm.
;;; options incude
;;;   :title (default "Alert")
;;;   :text (defaut "Alert!") -- not really optional.
;;;
(chaos::define-tk-function chaos::tk-alert "chaos:alert")

;;; TK-PROMPT options...
;;; prompt the user for information.
;;; options are:
;;;  :text (default "Enter a value:")
;;;  :default (defeult "")
;;;  :cancelvalue (default "")
;;;  :file (default 0)
;;;  :title (default "Prompt")
;;; if :file is given with value 1, the Tab key will do filename completion.
;;;
(chaos::define-tk-function chaos::tk-prompt "chaos:prompt")

;;; TK-PROMPT-FONT options
;;; promt for a font (via xfontsel)
;;; options include:
;;;  :prompt (default "Font:", but currently ignored)
;;;  :pattern (default "*")
;;; usagetof xfontsel (`whit' button) not obvious!
;;;
(chaos::define-tk-function chaos::tk-promt-font "chaos:prompt_font")

;;; TK-PROMPT-TCL
;;; prompt for a tcl command and execute it
;;;
(defun chaos::tk-prompt-tcl ()
  (tk-do "chaos:prompt_tcl"))

;;; TK-PROMPT-UNIX
;;; prompt for a unix command and execute it
;;;
(defun chaos::tk-prompt-unix ()
  (tk-do "chaos:prompt_unix"))

;;; TK-SELECT-FILE-NAME
;;;
(defun chaos::tk-select-file-name (&optional allow-non-exist)
  (let ((*default-timeout* most-positive-fixnum))
    (multiple-value-bind (result ok?)
	(if allow-non-exist
	    (tk-do "FileSelectGetFile 1")
	    (tk-do "FileSelectGetFile 0"))
      (if (and ok? (< 0 (length result)))
	  (truename (pathname result))
	  nil))))

;;; TK-TEXT-INSERT w text 
;;;  insert text into w at insert point.
;;;  * detects if tags are being used and uses "chaos:tag:insert_string".
;;;  * handles deletion of selection if needed.
;;;
(chaos::define-tk-function chaos::tk-text-insert "chaos:text:insert_string")

;;; TK-TEXT-MOVE w index
;;; move insert mark in w to index
;;;
(chaos::define-tk-function chaos::tk-text-move "chaos:text:move")

;;; TK-TEXT-DELETE w from to
;;; delete from index from to index to in w.
;;;
(chaos::define-tk-function chaos::tk-text-delete "chaos:text:delete")

;;; TK-TEXT-REPLACE w from to string
;;; replace range with string, preserving tags at from
;;;
(chaos::define-tk-function chaos::tk-text-replace "chaos:text:replace")

;;; TK-TEXT-MARK-MODIFIED w
;;; mark widget w as modified
;;;
(chaos::define-tk-function chaos::tk-text-mark-modified "chaos:text:mark_dirty")

;;; TK-TEXT-MARK-CLEAN w
;;; mark widget w as un-modified
;;;
(chaos::define-tk-function chaos::tk-text-mark-clean "chaos:text:mark_clean")

;;; TK-TEXT-IS-MODIFIED w
;;; returns true if w is modified else nil
;;;
(chaos::define-tk-function chaos::tk-text-is-modified "chaos:text:is_dirgy" boolean)

;;; TK-TEXT-HAS-SELECTION w
;;; returns true if slectin made in w, else nil
;;;
(chaos::define-tk-function chaos::tk-text-has-selection "chaos:text:has_selection"
  boolean)

;;; TK-TEXT-INSERT-TOUCHES-SELECTION w
;;; returns t if selection exists in w and insert is inside or next to
;;; it (as will be the case if you just made the selection with the mouse).
;;;
(chaos::define-tk-function chaos::tk-text-insert-touches-selection
    "chaos:text:insert_touches_selection" boolean)


;;; TK-MAKE-TEXT-WINDOW parent entry-name &optional show-title
;;;
(defun chaos::tk-make-text-window (&key parent
					entry-name
					(width 60)
					(background "gray85")
					(frameback "gray90")
					(height 12)
					(relief "sunken")
					(font "{-*-new*-medium-r-normal--14-100-*}")
					(show-title 0))
  (let (res)
    (setf res (tk-do "chaos:make-text-window -parent " :|| parent
			 " -entryname " :|| entry-name
			 " -width " :|| width
			 " -height " :|| height
			 " -background " :|| background
			 " -frameback " :|| frameback
			 " -relief " :|| relief
			 " -showtitle " :|| show-title
			 " -font " :|| font
			 ))

    (values-list (chaos::parse-with-delimiter res #\Space))))

;;; TK-TEXT-SEARCH&MARK text-widget string tag &optional delete-previous-tag
;;;
(defun chaos::tk-text-search&mark (w string tag &optional show-title)
  (if show-title
      (tk-do "chaos:TextSearchMark " :|| w " {" :|| string :|| "}"
	     :|| 1space-string tag " 1")
      (tk-do "chaos:TextSearchMark " :|| w :|| " {" :|| string :|| "}"
	     :|| 1space-string tag)))

;;; TERPRI-WINDOW text-window &optional (n 1)
;;;
(defun chaos::terpri-window (window &optional (n 1))
  (tk-do "chaos:TerpriWindow " window 1space-string :|| n))


;;; CREATE-TOP-FRAME-IF-NEED
;;;
(defun chaos::create-top-frame-if-need (parent name &optional unique-suffix)
  (let (top
	frame)
    (cond (parent (setf top parent)
		  (setf frame (conc parent name))
		  ;; top frame.
		  (unless (winfo :exists frame :return 'boolean)
		    (frame frame :borderwidth 4)))
	  (t (setf top (conc name (or unique-suffix (gensym "foo"))))
	     (unless (winfo :exists top :return 'boolean)
	       (toplevel top))
	     (setf frame (conc top name))
	     (unless (winfo :exists frame :return 'boolean)
	       (frame frame :borderwidth 4))))
    (values top frame)))

;;; EOF
