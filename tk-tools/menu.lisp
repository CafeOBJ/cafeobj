;;;-*- Mode:LISP; Package:TK; Base:10; Syntax:Common-lisp -*-
(in-package "TK")
#|==============================================================================
				 System: CHAOS
			      Module: tools.KERNEL
				File: menu.lisp
				  Version: 1.0
					
sawada@sra.co.jp
==============================================================================|#
(defparameter chaos::menu-title-font ':Adobe-courier-medium-r-normal--14-140-*)
(defparameter chaos::menu-font ':Adobe-helvetica-medium-r-normal--12-120-*)

(defun chaos::make-menus (mf menu-list
			     &key
			     (menu-button-font chaos::menu-title-font)
			     (menu-font chaos::menu-font)
			     (border-width 4)
			     (relief "groove")
			     (side "top")
			     (fill "x"))
  (if (winfo :exists mf :return 'boolean) (destroy mf))
  (frame mf :bd border-width :relief relief)
  (pack mf :side side :fill fill)
  (let ((menu-buttons nil))
    (dolist (mb menu-list)
      (let* ((menu-button (conc mf '|.| (car mb)))
	     (mlist (cdr mb))
	     (text (or (cadr (assoc 'text mlist)) "Unknown"))
	     (underline (or (cadr (assoc 'underline mlist)) 0))
	     (entries (cdr (assoc 'menu mlist)))
	     (menu (conc menu-button '|.m|)))
	(if (winfo :exists menu-button :return 'boolean)
	    (destroy menu-button))
	(menubutton menu-button :text text :underline underline
		    :menu menu :font menu-button-font)
	(push menu-button menu-buttons)
	(menu menu :font menu-font)
	(dolist (e entries)
	  (case (car e)
	    (command 
	     (let ((label (cadr (assoc 'label (cdr e))))
		   (command (cadr (assoc 'command (cdr e))))
		   (accelerator (cadr (assoc 'accelerator (cdr e)))))
	       (if accelerator
		   (funcall menu :add 'command
			    :label label
			    :accelerator accelerator
			    :command command)
		   (funcall menu :add 'command
			    :label label
			    :command command))))
	    (separator (funcall menu :add 'separator))
	    (checkbutton
	     (let ((label (or (cadr (assoc 'label (cdr e))) 'unknown))
		   (variable (or (cadr (assoc 'variable (cdr e))) '(boolean unknown)))
		   (accelerator (cadr (assoc 'accelerator (cdr e)))))
	       (if accelerator
		   (funcall menu :add 'checkbutton
			    :label label
			    :accelerator accelerator
			    :variable variable)
		   (funcall menu :add 'checkbutton
			    :label label
			    :variable variable))))
	    (t (warining "Menu type ~a is not supported yet" (car e)))))))
    (apply 'pack (append (nreverse menu-buttons) '(:side "left")))))

	
;;; EOF
