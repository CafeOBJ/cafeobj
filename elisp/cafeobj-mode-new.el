;From: Razvan Diaconescu <diacon@jaist.ac.jp>
;Date: Wed, 24 Sep 97 04:14:00 GMT
;Message-Id: <9709240414.AA09049@is27e0s07.jaist.ac.jp>
;To: dlucanu@infoiasi.ro, sawada@sra.co.jp
;Subject:  cafeobj-mode again
;Content-Type: text
;Content-Length: 63479

;Dear Toshimi and Dorel,

;If you are fed up it my messages on the cafeobj-mode topic please
;ignore this.

;I just fixed a couple of small bugs in the kb7 part of the
;cfeobj-mode. Now, if you move between fields with TAB you get
;automatic pluralisation for var/op/bop (when necessary, of course) and
;a warning message in the minibuffer if for an operation the number of
;underscores doesnt agree with the number of sorts in the arity.

;Remember also that my menu works only with FSF version of emacs.

;Best regards,
;Razvan
;-------------------------cut here-----------
;;; cafeobj-mode.el --- CafeOBJ code editing and Interaction with
;;;                     CafeOBJ interpreter.
;;; Copyleft: verbatim copies of this file may be freely redistributed.
;;; This file is distributed `as is', without warranties of any kind.
;;;
;;;                                   Toshimi Sawada <sawada@sra.co.jp>
;;;
;;; $Id: cafeobj-mode-new.el,v 1.1 2003-12-13 12:43:03 sawada Exp $
;;;    ++ KB7 style commands for CafeOBJ constructs by Razvan Diaconescu
;;; Keywords: cafeobj chaos languages processes tools
;;;
;;; BRIEF DESCRIPTION:
;;; CafeOBJ-mode supports formatting CafeOBJ source codes and sending of
;;; declarations/regions/files to a CafeOBJ interpreter. An interpreter 
;;; (see variable `cafeobj-default-application') will be started if you try
;;; to send some code and none is running. You can use the process-buffer
;;; (named after the application you chose) as if it were an
;;; interactive shell. See the documentation for `comint.el' for
;;; details.
;;; *NOTE* : This mode supports Chaos with CafeOBJ syntax only.

;;; ====== DESCRIPTION =========================================================
;;; 
;;; USAGE:
;;; The following statements, placed in your .emacs file or
;;; site-init.el, will cause this file to be autoloaded, and
;;; cafeobj-mode invoked, when visiting .mod files (assuming this file is
;;; in your load-path):
;;;
;;;	(autoload 'cafeobj-mode "cafeobj-mode" "CafeOBJ mode." t)
;;;	(setq auto-mode-alist
;;;	      (cons '("\\.mod$" . cafeobj-mode) auto-mode-alist))
;;;
;;; and, also the following is handy for running CafeOBJ interpreter:
;;;
;;;     (autoload 'cafeobj "cafeobj-mode" "Run CafeOBJ interpreter." t)
;;;
;;; If you want font-lock support for CafeOBJ source code (a.k.a. syntax
;;; coloring, highlighting), add this to your .emacs file:
;;;  (cond ((string-match "XEmacs\\Lucid" emacs-version)
;;;         ;; XEmacs
;;;         (add-hook 'cafeobj-mode-hook 'turn-on-font-lock))
;;;        (t ;; FSF19.XX, assumes the version better than 19.28..
;;;           (add-hook 'cafeobj-mode-hook (function
;;;                                          (lambda () (font-lock-mode 1))))))
;;;
;;; Notes on FONT-LOCK:
;;; You better be sure you're version of Emacs supports
;;; font-lock-mode!  As of this writing, the latest Emacs and XEmacs
;;; 19's do. This file is known to be run on Emacs19.28(Mule 2.3), and
;;; XEmacs(20.02). 
;;;
;;; KEY BINDINGS:
;;; To see all the keybindings for folding mode, look at `cafeobj-setup-keymap'
;;; or start `cafeobj-mode' and type `\C-h m'.
;;; The keybindings are defined with prefixed by 'cafeobj-prefix-key',
;;; the default for `cafeobj-prefix-key' is `\C-c', which is the conventional
;;; prefix for major-mode commands.
;;; You can customise the keybindings either by setting `choas-prefix-key'
;;; or by putting the following in your .emacs
;;; 	(setq cafeobj-mode-map (make-sparse-keymap))
;;; and
;;; 	(define-key cafeobj-mode-map <your-key> <function>)
;;; for all the functions you need.
;;;
;;; ABBRIVE-MODE:
;;; CafeOBJ mode provides a mode-specific abbrev table 'cafeobj-mode-abbrev-table',
;;; and there defined some abbriviations already.
;;; You can use abbrev by `M-x abbrev-mode' or putting the following in your
;;; .emacs
;;;    (add-hook 'cafeobj-mode-hook (function (lambda () (abbrev-mode 1))))
;;;
;;; The predefined abbribiations are minimum, these are derived from my own
;;; experience. I want these definitions to be useful for most of the users,
;;; but ofcourse, you may feel it does not match to your taste. In that case,
;;; add your own definitions for preventing my deinitions.
;;; To edit the entire table, `M-x edit-abbrevs' and `M-x write-abbrev-file'
;;; are handy. Here is an example of adding some extra abbreviations:
;;; I want the following abbreviations:
;;;     "mod"	->  "module"
;;;     "mod*"  ->  "module*"
;;;     "mod!"  ->  "module!"
;;;     "obj"	->  "module!"
;;;     "th"	->  "module*"
;;; For this, we can use `M-x edit-abbrevs' and adds the above definitions in
;;; cafeobj-abbrev-table like this:
;;;
;;; (cafeobj-mode-abbrev-table)
;;;
;;;    "mod"	 0     "module"
;;;    "m*"	 0     "module* "
;;;    "m!"      0     "module! "         
;;;    "obj"     0     "module!"
;;;    "th"      0     "module*"
;;;    "comm"    0     "commutative"
;;;            :
;;;            :
;;; After editting, type `C-c C-c'(M-x edit-abbrevs-redefine) to install
;;; abbrev definitions as specified. 
;;; Then use `M-x write-abbrev-file' specifying ~/.abbrev_deffs to
;;; the target file name, and adds a line in my .emacs
;;; (read-abbrev-file "~/.abbrev_defs").
;;; See Emacs manual of Infos for detail.
;;;
;;; CUTOMIZABLE VARIABLES:
;;; You may want to customize the following variables, see the comment strings
;;; for the descriptions of these variables.
;;;
;;; 	cafeobj-always-show
;;;	cafeobj-mode-map
;;;	cafeobj-prefix-key
;;;	cafeobj-mode-hook
;;; 	cafeobj-default-application
;;; 	cafeobj-default-command-switches
;;;     cafeobj-decl-keyword-face
;;;     cafeobj-keyword-face
;;;     cafeobj-command-face
;;;     cafeobj-comment-face
;;;     cafeobj-indent-level
;;;     cafeobj-brace-imaginary-offset
;;;     cafeobj-brace-offset
;;;     cafeobj-psort-indent
;;;     cafeobj-continued-statement-offset
;;;     cafeobj-continued-brace-offset
;;;
;;; see document strings for some brief description of each variable.
;;;

(require 'comint)

;;; -----------------------
;;; Customizable variables _____________________________________________________
;;; -----------------------

(defvar cafeobj-always-show t
  "*Non-nil means display cafeobj-process-buffer after sending a command.")

(defvar cafeobj-mode-map nil
  "Keymap used with cafeobj mode.")

(defvar cafeobj-prefix-key "\C-c"
  "Prefix for all cafeobj-mode commands.")

(defvar cafeobj-mode-hook nil
  "Hooks called when cafeobj mode fires up.")

(defvar cafeobj-default-application "cafeobj"
  "Default Chaos (CafeOBJ) dialect to run in chaos subprocess.")

(defvar cafeobj-default-command-switches nil
  "Command switches for `cafeobj-default-application'.
Should be a list of strings which will be given to the cafeobj process when star up.")

;;; below, we define `faces' of various CafeOBJ syntactic categories.
;;; these are used in font-lock mode for displaying CafeOBJ sources.
;;; You may wish to change these values to suit your taste; set them
;;; in your .emacs or elsewhere which is evaluated BEFORE this file.

(defvar cafeobj-decl-keyword-face 'bold
  "a face used for top level declaration keywords, such as module, view.")
(defvar cafeobj-keyword-face font-lock-function-name-face
  "a face used for displaying keywords of module constructs, ex. op, eq ..")
(defvar cafeobj-command-face font-lock-keyword-face
  "a face used for displaying top-level commands, show, describe, open, and so on.")
(defvar cafeobj-comment-face font-lock-comment-face
  "a face for comment lines.")

;;; INDENTATION CONTROL

(defvar cafeobj-indent-level 2
  "*Indentation of CafeOBJ statements with respect to containing block.")
(defvar cafeobj-brace-imaginary-offset 0
  "*Imagined indentation of a CafeOBJ open brace that actually follows a statement.")
(defvar cafeobj-brace-offset 0
  "*Extra indentation for braces, compared with other text in same context.")
(defvar cafeobj-psort-indent 5
  "*Indentation level of principal-sort declaration of CafeOBJ.")
(defvar cafeobj-continued-statement-offset 2
  "*Extra indent for lines not starting new statements.")
(defvar cafeobj-continued-brace-offset 0
  "*Extra indent for substatements that start with open-braces.
This is in addition to cafeobj-continued-statement-offset.")

;;; ---------------------------------
;;; globals for internal use only....
;;; ---------------------------------

(defvar cafeobj-process nil
  "The active chaos subprocess corresponding to current buffer.")

(defvar cafeobj-process-buffer nil
  "Buffer used for communication with chaos subprocess for current buffer.")

(defvar cafeobj-region-start (make-marker)
  "Start of special region for chaos communication.")

(defvar cafeobj-region-end (make-marker)
  "End of special region for chaos communication.")

;;; -----------------
;;; Portability stuff___________________________________________________________
;;; -----------------

(defconst cafeobj-xemacs-p (string-match "XEmacs\\|Lucid" emacs-version))

(defmacro cafeobj-define-key (fsf-key definition &optional xemacs-key)
  `(define-key cafeobj-mode-map
    ,(if xemacs-key
	 `(if cafeobj-xemacs-p ,xemacs-key ,fsf-key)
	 fsf-key)
    ,definition))

(defvar del-back-ch (car (append (where-is-internal 'delete-backward-char)
				 (where-is-internal 'backward-delete-char-untabify)))
  "Character generated by key bound to delete-backward-char.")

(and (vectorp del-back-ch) (= (length del-back-ch) 1) 
     (setq del-back-ch (aref del-back-ch 0)))

;;;---------------------------
;;; CafeOBJ Keywords/Commands __________________________________________________
;;; essential syntactic structures are defined here.
;;;---------------------------

(defconst cafeobj-comment-pat "\\(--\\|\\*\\*\\)[ \t\n]+")

(defconst cafeobj-keywords
    '("op" "ops" "\\[" "\\]" "\\*\\[" "\\]\\*"
      "bop" "pred" "bops" "bpred"
      "imports" "protecting" "pr"
      "extending" "ex" "using" "us"
      "signature" "axioms" 
      "var" "vars"
      "eq" "cq" "ceq" 
      "bq" "beq" "bcq" "bceq" 
      "trans" "trns" "ctrans" "ctrns" 
      "btrans" "btrns" "bctrans" "bctrns"
      "class" "record" "attr"
      "view"
      "sort" "hsort"
      "psort" "principal-sort")
  "keywords appearing inside module declaration or view declaration."
  )

(defconst cafeobj-keyword-pat
    (mapconcat 'identity cafeobj-keywords "\\|"))

(defun looking-at-cafeobj-keyword-pat ()
  (looking-at cafeobj-keyword-pat))

(defconst cafeobj-commands
    '("let" "red" "reduce" "input" "in" 
      "execute" "exec" "make"
      "apply" "start" "match"
      "parse"
      "select"
      "set"
      "show"
      "describe"
      "sh"
      "choose" "open" "close"
      "desc" "eof"
      "require" "provide")
  "CafeOBJ top-level commands")

(defconst cafeobj-command-pat
    (mapconcat 'identity cafeobj-commands "\\|"))

(defun looking-at-cafeobj-command-pat ()
  (looking-at cafeobj-command-pat))

(defconst cafeobj-top-keywords
    '("op" "ops" "bop" "bops" "pred"  "bpred"
      "var" "vars"
      "eq" "cq" "ceq" 
      "bq" "beq" "bcq" "bceq" 
      "trans" "trns" "ctrans" "ctrns" 
      "btrans" "btrns" "bctrans" "bctrns"
      "class" "record" "attr"
      "\\[" "\\]")
  "CafeOBJ keyowrds may apper at top-level.")

(defun looking-at-cafeobj-top-keywords ()
  (looking-at cafeobj-top-keywords))

(defconst cafeobj-top-key-pat
    (mapconcat 'identity cafeobj-top-keywords "\\|"))

(defconst cafeobj-top-decl-pat 
    "^\\(module\\|mod\\|module\*\\|mod\*\\|module!\\|mod!\\|view\\)")

(defun looking-at-cafeobj-top-decl ()
  (looking-at "\\(module\\|mod\\|module\*\\|mod\*\\|module!\\|mod!\\|view\\)")
  )

(defconst cafeobj-block-start-pat
    "\\(signature\\|axioms\\|imports\\|record\\|class\\)")

(defun looking-at-cafeobj-block-start-pat ()
  (looking-at "\\(signature\\|axioms\\|imports\\|record\\|class\\)"))
       
(defun looking-at-cafeobj-module-decl ()
  (looking-at "module\\|mod\\|module\*\\|mod\*\\|module!\\|mod!"))

(defun looking-at-cafeobj-view-decl ()
  (looking-at "view"))

;;;----------
;;; FONT-LOCK___________________________________________________________________
;;;----------

(defun get-cafeobj-face (name)
  (cond (cafeobj-xemacs-p (symbol-value name))
	(t (identity name))))

(defvar cafeobj-font-lock-keywords nil
  "Additional expressions to highlight in CafeOBJ mode.")
(setq cafeobj-font-lock-keywords
      (list
       ;; comments
       (cons "^--.*" (get-cafeobj-face 'cafeobj-comment-face))
       (cons "^\\*\\*.*" (get-cafeobj-face 'cafeobj-comment-face))
       (cons "\\s-\\(--\\|\\*\\*\\|-->\\|\\*\\*>\\)[ \n\t].*"
	     (get-cafeobj-face 'cafeobj-comment-face))
       ;; keywords not at beginning of line
       (cons (concat "\\s-\\(" cafeobj-keyword-pat "\\)[ \n\t]")
	     (get-cafeobj-face 'cafeobj-keyword-face))
       ;; commands at beginning of line
       (cons (concat "^\\(" cafeobj-command-pat "\\)[ \n\t]")
	     (get-cafeobj-face 'cafeobj-command-face))
       ;; module
       (cons "^mod[a-z\!\*]*[ \t]"
	     (get-cafeobj-face 'cafeobj-decl-keyword-face))
       ;; view
       (cons "^view" (get-cafeobj-face 'cafeobj-decl-keyword-face))
       ;; declaration appering at the top level. 
       (cons (concat "^\\(" cafeobj-top-key-pat "\\)[ \n\t]")
	     (get-cafeobj-face 'cafeobj-keyword-face))
       ;; module name
       ;; '("\\bmod[a-z\!\*]*[ \t]+\\([a-zA-Z0-9_-\!\*\$\%\&\#\=]*\\)"
       ;;  . font-lock-function-name-face)
       ;; view name
       ;;'("\\bview[ \t]+\\([a-zA-Z_]+[a-zA-Z0-9_-\!\*\$\%\&\#\=]*\\)"
       ;;  . font-lock-type-face)
       ))

;;; XEmacs handles the following, but FSF19 not
(cond (cafeobj-xemacs-p
       (put 'cafeobj-mode 'font-lock-defaults '(cafeobj-font-lock-keywords)))
      (t
       ;; FSF19, we must explicitry set the value of 'font-lock-keywords'
       ;; this will be done in 'cafeobj-mode'.
       ))

;;; --------------------
;;; Default Key Bindings________________________________________________________
;;; --------------------

(defun cafeobj-setup-keymap ()
  "Set up keymap for cafeobj mode.
If the variable `cafeobj-prefix-key' is nil, the bindings go directly
to `cafeobj-mode-map', otherwise they are prefixed with `cafeobj-prefix-key'."
  (setq cafeobj-mode-map (make-sparse-keymap))
  ;; 
  (let ((map (if cafeobj-prefix-key
		 (make-sparse-keymap)
		 cafeobj-mode-map)))
    ;; indentation
    (define-key cafeobj-mode-map [?}] 'cafeobj-electric-brace)
    ;; communication
    (define-key map "i" 'cafeobj-send-line)
    (define-key map "e" 'cafeobj-send-decl)
    (define-key map "r" 'cafeobj-send-region)
    (define-key map "l" 'cafeobj-send-buffer)
    (define-key map "[" 'cafeobj-beginning-of-decl)
    (define-key map "]" 'cafeobj-end-of-decl)
    (define-key map "q" 'cafeobj-kill-process)
    (define-key map "s" 'cafeobj-show-process-buffer)
    (define-key map "h" 'cafeobj-hide-process-buffer)
    ;;
    (if cafeobj-prefix-key
	(define-key cafeobj-mode-map cafeobj-prefix-key map))
    ))

(cafeobj-setup-keymap)

;;; -------------
;;; MENU SUPPORTS_______________________________________________________________
;;; -------------

;; For XEmacs 
(defvar cafeobj-mode-popup-menu nil)
(defvar cafeobj-mode-menubar-menu nil)

;; For FSF19
(defvar cafeobj-mode-menu nil
  "Keymap for cafeobj-mode's menu.")
(defvar cafeobj-edit-menu nil
  "Keymap for cafeobj edit menu.")
(defvar cafeobj-trans-menu nil
  "keymap for transitions editing")
(defvar cafeobj-eq-menu nil
  "keymap for equations editing")
(defvar cafeobj-op-menu nil
  "keymap for operations editing")
(defvar cafeobj-sort-menu nil
  "keymap for sort editing")
(defvar cafeobj-import-menu nil
  "keymap for module imports editing")
(defvar cafeobj-view-menu nil
  "keymap for view editing")
(defvar cafeobj-module-menu nil
  "keymap for module definition editing")

(cond (cafeobj-xemacs-p
       (setq cafeobj-mode-popup-menu
	     (purecopy '("CafeOBJ Interaction Menu"
			 ["Evaluate This Declaration"
			  cafeobj-send-decl          t]
			 ["Evaluate Current Line" cafeobj-send-line  t]
			 ["Evaluate Entire Buffer" cafeobj-send-buffer t]
			 ["Evaluate Region"  cafeobj-send-region
			  (region-exists-p)]
			 "---"			 
			 ["Comment Out Region" comment-region (region-exists-p)]
			 ["Indent Region"	indent-region	(region-exists-p)]
			 ["Indent Line"		cafeobj-indent-line t]
			 ["Beginning of Declaration"
			  cafeobj-beginning-of-decl t]
		      )))
       (setq cafeobj-mode-menubar-menu
	     (purecopy (cons "CafeOBJ" (cdr cafeobj-mode-popup-menu)))))
      (t ;; 
       (setq cafeobj-mode-menu (make-sparse-keymap "CafeOBJ-Eval"))
       ;; Interaction menu
       ;; interaction with CafeOBJ interpreter.
       ;;
       (define-key cafeobj-mode-map [menu-bar cafeobj-mode]
	 (cons "CafeOBJ" cafeobj-mode-menu))
       (define-key cafeobj-mode-map [menu-bar cafeobj-mode send-current-line]
	 '("Evaluate Current Line" . cafeobj-send-line))
       (define-key cafeobj-mode-map [menu-bar cafeobj-mode send-region]
	 '("Evaluate CafeOBJ-Region" . cafeobj-send-region))
       (define-key cafeobj-mode-map [menu-bar cafeobj-mode send-proc]
	 '("Evaluate This Declaration" . cafeobj-send-decl))
       (define-key cafeobj-mode-map [menu-bar cafeobj-mode send-buffer]
	 '("Send Buffer" . cafeobj-send-buffer))
       ;;
       ;; edit menu
       ;;
       (setq cafeobj-edit-menu (make-sparse-keymap "CafeOBJ-Edit"))
       (define-key cafeobj-mode-map [menu-bar cafeobj-edit]
	 (cons "CafeOBJ-Edit" cafeobj-edit-menu))
       (define-key cafeobj-mode-map [menu-bar cafeobj-edit beginning-of-decl]
	 '("Beginning Of Proc" . cafeobj-beginning-of-decl))
       (define-key cafeobj-mode-map [menu-bar cafeobj-edit comment-region]
	 '("Comment Out Region" . comment-region))
       (define-key cafeobj-mode-map [menu-bar cafeobj-edit indent-region]
	 '("Indent Region" . indent-region))
       (define-key cafeobj-mode-map [menu-bar cafeobj-edit indent-line]
	 '("Indent Line" . cafeobj-indent-command))
       (define-key cafeobj-mode-map [menu-bar cafeobj-edit beginning-of-decl]
	 '("Beginning of Declaration" . cafeobj-beginning-of-decl))
       (define-key cafeobj-mode-map [menu-bar cafeobj-edit undo]
	 '("Undo" . cafeobj-kb7-undo))
       ;;
       ;; kb7-style syntax-oriented editing commands
       ;;
       (define-key cafeobj-mode-map [menu-bar cafeobj-edit separator-trans]
	 '("--"))
       (define-key cafeobj-mode-map [menu-bar cafeobj-edit trans]
	 '("Transition" . cafeobj-trans-menu))
       (define-key cafeobj-mode-map [menu-bar cafeobj-edit eq]
	 '("Equation" . cafeobj-eq-menu))
       (define-key cafeobj-mode-map [menu-bar cafeobj-edit var]
	 '("Variable" . var))
       (define-key cafeobj-mode-map [menu-bar cafeobj-edit op]
	 '("Operation" . cafeobj-op-menu))
       (define-key cafeobj-mode-map [menu-bar cafeobj-edit sort]
	 '("Sort" . cafeobj-sort-menu))
       (define-key cafeobj-mode-map [menu-bar cafeobj-edit import]
	 '("Import" . cafeobj-import-menu))
       (define-key cafeobj-mode-map [menu-bar cafeobj-edit separator-view]
	 '("--"))
       (define-key cafeobj-mode-map [menu-bar cafeobj-edit view]
	 '("View" . cafeobj-view-menu))
       (define-key cafeobj-mode-map [menu-bar cafeobj-edit module]
	 '("Module" . cafeobj-module-menu))
       ))

;;; transition menu (FSF)
(setq cafeobj-trans-menu (make-sparse-keymap "Transition"))
(defalias 'cafeobj-trans-menu (symbol-value 'cafeobj-trans-menu))
(define-key cafeobj-mode-map [menu-bar cafeobj-edit]
   (cons "Transition" cafeobj-trans-menu))
(define-key cafeobj-trans-menu [ctrans]
    '("conditional..." . ctrans))
(define-key cafeobj-trans-menu [trans]
     '("simple..." . trans))

;;; equation menu (FSF)
(setq cafeobj-eq-menu (make-sparse-keymap "Equation"))
(defalias 'cafeobj-eq-menu (symbol-value 'cafeobj-eq-menu))
(define-key cafeobj-mode-map [menu-bar cafeobj-edit]
   (cons "Equation" cafeobj-eq-menu))
(define-key cafeobj-eq-menu [bcq]
   '("cond behavioural..." . bcq))
(define-key cafeobj-eq-menu [beq]
   '("behavioural..." . beq))
(define-key cafeobj-eq-menu [cq]
   '("conditional..." . cq))
(define-key cafeobj-eq-menu [eqq]
   '("simple..." . eqq))

;;; operation menu (FSF)
(setq cafeobj-op-menu (make-sparse-keymap "Operation"))
(defalias 'cafeobj-op-menu (symbol-value 'cafeobj-op-menu))
(define-key cafeobj-mode-map [menu-bar cafeobj-edit]
   (cons "Operation" cafeobj-op-menu))
(define-key cafeobj-op-menu [bop]
    '("behavioural..." . bop))
(define-key cafeobj-op-menu [op]
     '("algebraic..." . op))

;;; sort menu (FSF)
(setq cafeobj-sort-menu (make-sparse-keymap "Sort"))
(defalias 'cafeobj-sort-menu (symbol-value 'cafeobj-sort-menu))
(define-key cafeobj-mode-map [menu-bar cafeobj-edit]
   (cons "Sort" cafeobj-sort-menu))
(define-key cafeobj-sort-menu [hsort]
    '("hidden..." . hsort))
(define-key cafeobj-sort-menu [vsort]
    '("visible..." . vsort))

;;; import menu (FSF)
(setq cafeobj-import-menu (make-sparse-keymap "Import"))
(defalias 'cafeobj-import-menu (symbol-value 'cafeobj-import-menu))
(define-key cafeobj-mode-map [menu-bar cafeobj-edit]
   (cons "Import" cafeobj-import-menu))
(define-key cafeobj-import-menu [using]
    '("using..." . using))
(define-key cafeobj-import-menu [ex]
     '("extending..." . ex))
(define-key cafeobj-import-menu [pr]
     '("protecting..." . pr))

;;; view menu (FSF)
(setq cafeobj-view-menu (make-sparse-keymap "View"))
(defalias 'cafeobj-view-menu (symbol-value 'cafeobj-view-menu))

;;; module menu (FSF) 
(setq cafeobj-module-menu (make-sparse-keymap "Module"))
(defalias 'cafeobj-module-menu (symbol-value 'cafeobj-module-menu))
(define-key cafeobj-module-menu [modd]
     '("either..." . modd))
(define-key cafeobj-module-menu [mod*]
     '("loose semantics..." . mod*))
(define-key cafeobj-module-menu [mod!]
     '("initial semantics..." . mod!))

;;; ------------
;;; CafeOBJ Mode________________________________________________________________
;;; ------------

(defvar cafeobj-mode-abbrev-table nil
  "Abbrev table in use in CafeOBJ mode.")
;;; some default abbreviations define here
(if cafeobj-mode-abbrev-table
    nil
    (define-abbrev-table 'cafeobj-mode-abbrev-table
	'(("btrns" "btrans" nil 0)
	  ("bcq" "bceq" nil 0)
	  ("compat" "compatibility" nil 0)
	  ("psort" "principal-sort" nil 0)
	  ("req" "require" nil 0)
	  ("sh" "show" nil 0)
	  ("verb" "verbose" nil 0)
	  ("reg" "regularize" nil 0)
	  ("import" "imports" nil 0)
	  ("cq" "ceq" nil 0)
	  ("red" "reduce" nil 0)
	  ("strat" "strategy" nil 0)
	  ("us" "using" nil 0)
	  ("btrn" "btrans" nil 0)
	  ("btr" "btrans" nil 0)
	  ("reconst" "reconstruct" nil 0)
	  ("chk" "check" nil 0)
	  ("trns" "trans" nil 0)
	  ("swit" "swithces" nil 0)
	  ("bq" "beq" nil 0)
	  ("desc" "describe" nil 0)
	  ("bctr" "bctrans" nil 0)
	  ("incl" "include" nil 0)
	  ("bctrn" "bctrans" nil 0)
	  ("ex" "extending" nil 0)
	  ("axs" "axioms" nil 0)
	  ("pr" "protecting" nil 0)
	  ("bctrns" "bctrans" nil 0)
	  ("pat" "pattern" nil 0)
	  ("recon" "reconstruct" nil 0)
	  ("prov" "provide" nil 0)
	  ("sel" "select" nil 0)
	  ("sig" "signature" nil 0)
	  ("sign" "signature" nil 1)
	  ("cond" "conditions" nil 0)
	  ("imp" "imports" nil 0)
	  ("comp" "compatibility" nil 0)
	  ("swi" "switch" nil 0)
	  ("reconstr" "reconstruct" nil 0)
	  ))
    )


(defvar cafeobj-mode-syntax-table nil
  "Syntax table in use in cafeobj-mode buffers.")

(if cafeobj-mode-syntax-table
    ()
  (setq cafeobj-mode-syntax-table (make-syntax-table))
  (mapcar (function
	   (lambda (x) (modify-syntax-entry
			(car x) (cdr x) cafeobj-mode-syntax-table)))
	  '(( ?\( . "()" ) ( ?\) . ")(" )
	    ( ?\[ . "(]" ) ( ?\] . ")[" )
	    ( ?\{ . "(}" ) ( ?\} . "){" )
	    ;; underscore is word class
	    ( ?\_ . "w" )
	    ( ?\" . "\"" )	; double quote is string quote too
	    ( ?\n . ">"))
	  ))

(defun cafeobj-mode ()
  "Major mode for editing CafeOBJ programs.
The following keys are bound:
\\{cafeobj-mode-map}
"
  (interactive)
  (let (s)
    (kill-all-local-variables)
    (setq major-mode 'cafeobj-mode)
    (setq mode-name "CafeOBJ")
    ;; keymap
    (or cafeobj-mode-map (cafeobj-setup-keymap))
    (use-local-map cafeobj-mode-map)
    ;; abbrev
    (setq local-abbrev-table cafeobj-mode-abbrev-table)
    ;; settting menu.
    (if cafeobj-xemacs-p
	(setq mode-popup-menu
	      cafeobj-mode-popup-menu)
	(progn
	  (define-key cafeobj-mode-map [menu-bar cafeobj-mode]
	    (cons "CafeOBJ-Eval" cafeobj-mode-menu))
	  (define-key cafeobj-mode-map [menu-bar cafeobj-edit]
	    (cons "CafeOBJ-Edit" cafeobj-edit-menu))
          ))
    ;;
    (set (make-local-variable 'cafeobj-process) nil)
    (set (make-local-variable 'cafeobj-process-buffer) nil)
    (make-local-variable 'cafeobj-default-command-switches)
    ;;
    (cond (cafeobj-xemacs-p
	   (make-local-variable 'font-lock-defaults))
	  (t (set (make-local-variable 'font-lock-keywords)
		  cafeobj-font-lock-keywords)))
    ;;
    (set (make-local-variable 'indent-line-function) 'cafeobj-indent-line)
    (set (make-local-variable 'comment-start) "-- ") ; obsolate? ... should be fixed.
    ;; todo --
    (set (make-local-variable 'comment-start-skip) "\\(\\(^\\|;\\)[ \t]*\\)--")
    ;; syntax-------
    (set-syntax-table cafeobj-mode-syntax-table)
    ;; (modify-syntax-entry ?# "<")
    (modify-syntax-entry ?\n ">")
    ;;
    (make-local-variable 'require-final-newline)
    (setq require-final-newline t)
    ;;
    (setq comment-column 32)
    (make-local-variable 'comment-start-skip)
    (make-local-variable 'parse-sexp-ignore-comments)
    (setq parse-sexp-ignore-comments t)
    ;; look for a #!.../cafeobj -f line at bob
    (save-excursion
      (goto-char (point-min))
      (if (looking-at "#![ \t]*\\([^ \t]*\\)[ \t]\\(.*[ \t]\\)-f")
	  (progn
	    (set (make-local-variable 'cafeobj-default-application)
		 (buffer-substring (match-beginning 1)
				   (match-end 1)))
	    (if (match-beginning 2)
		(progn
		  (goto-char (match-beginning 2))
		  (set (make-local-variable 'cafeobj-default-command-switches) nil)
		  (while (< (point) (match-end 2))
		    (setq s (read (current-buffer)))
		    (if (<= (point) (match-end 2))
			(setq cafeobj-default-command-switches
			      (append cafeobj-default-command-switches
				      (list (prin1-to-string s)))))))))
	;; if this fails, look for the #!/bin/csh ... exec hack
	(while (eq (following-char) ?#)
	  (forward-line 1))
	(or (bobp)
	    (forward-char -1))
	(if (eq (preceding-char) ?\\)
	    (progn
	      (forward-char 1)
	      (if (looking-at "exec[ \t]+\\([^ \t]*\\)[ \t]\\(.*[ \t]\\)*-f")
		  (progn
		    (set (make-local-variable 'cafeobj-default-application)
			 (buffer-substring (match-beginning 1)
					   (match-end 1)))
		    (if (match-beginning 2)
			(progn
			  (goto-char (match-beginning 2))
			  (set (make-local-variable
				'cafeobj-default-command-switches)
			       nil)
			  (while (< (point) (match-end 2))
			    (setq s (read (current-buffer)))
			    (if (<= (point) (match-end 2))
				(setq cafeobj-default-command-switches
				      (append cafeobj-default-command-switches
					      (list (prin1-to-string s)))))))))
		)))))
    ;;
    (if (and (featurep 'menubar)
	     current-menubar)
	(progn
	  ;; make a local copy of the menubar, so our modes don't
	  ;; change the global menubar
	  (set-buffer-menubar current-menubar)
	  (add-submenu nil cafeobj-mode-menubar-menu)))
    ;;
    (run-hooks 'cafeobj-mode-hook)))


;;; ----------------
;;; CafeOBJ Editting____________________________________________________________
;;; ----------------

(defconst cafeobj-auto-newline nil
  "*Non-nil means automatically newline before and after braces,
and after colons and semicolons, inserted in CafeOBJ code.")

(defconst cafeobj-tab-always-indent t
  "*Non-nil means TAB in C mode should always reindent the current line,
regardless of where in the line point is when the TAB command is used.")

(defun cafeobj-electric-brace (arg)
  "Insert character and correct line's indentation."
  (interactive "P")
  (let (insertpos)
    (if (and (not arg)
	     (eolp)
	     (or (save-excursion
		   (skip-chars-backward " \t")
		   (bolp))
		 (if cafeobj-auto-newline
		     (progn (cafeobj-indent-line) (newline) t)
		     nil)))
	(progn
	  (insert last-command-char)
	  (cafeobj-indent-line)
	  (if cafeobj-auto-newline
	      (progn
		(newline)
		;; (newline) may have done auto-fill
		(setq insertpos (- (point) 2))
		(cafeobj-indent-line)))
	  (save-excursion
	    (if insertpos (goto-char (1+ insertpos)))
	    (delete-char -1))))
    (if insertpos
	(save-excursion
	  (goto-char insertpos)
	  (self-insert-command (prefix-numeric-value arg)))
	(self-insert-command (prefix-numeric-value arg)))))

(defun cafeobj-beginning-of-block (&optional arg)
  "Move backward to the beginning of a CafeOBJ block structure.
With argument, do it that many times.  Negative arg -N
means move forward to Nth following beginning of declaration.
Returns t unless search stops due to beginning or end of buffer."
  (interactive "P")
  (or arg (setq arg 1))
  (let ((found nil)
	(ret t))
    (if (and (< arg 0)
	     (looking-at-cafeobj-block-start-pat))
	(forward-char 1))
    (while (< arg 0)
      (if (re-search-forward cafeobj-block-start-pat nil t)
	  (setq arg (1+ arg)
		found t)
	(setq ret nil
	      arg 0)))
    (if found
	(beginning-of-line))
    (while (> arg 0)
      (if (re-search-backward cafeobj-block-start-pat nil t)
	  (setq arg (1- arg))
	  (setq ret nil
		arg 0)))
    ret))

(defun cafeobj-beginning-of-decl (&optional arg)
  "Move backward to the beginning of a CafeOBJ top-level decl.
With argument, do it that many times.  Negative arg -N
means move forward to Nth following beginning of declaration.
Returns t unless search stops due to beginning or end of buffer."
  (interactive "P")
         (or arg (setq arg 1))
  (let ((found nil)
	(ret t))
    (if (and (< arg 0)
	     (looking-at cafeobj-top-decl-pat))
	(forward-char 1))
    (while (< arg 0)
      (if (re-search-forward cafeobj-top-decl-pat nil t)
	  (setq arg (1+ arg)
		found t)
	(setq ret nil
	      arg 0)))
    (if found
	(beginning-of-line))
    (while (> arg 0)
      (if (re-search-backward cafeobj-top-decl-pat nil t)
	  (setq arg (1- arg))
	  (setq ret nil
		arg 0)))
    ret))

(defun cafeobj-end-of-decl (&optional arg)
  "Move forward to next end of chaos declaration (or similar).
With argument, do it that many times.  Negative argument -N means move
back to Nth preceding end of proc.

This function just searches for a `}' at the beginning of a line."
  (interactive "P")
  (or arg
      (setq arg 1))
  (let ((found nil)
	(ret t))
    (if (and (< arg 0)
	     (not (bolp))
	     (save-excursion
	       (beginning-of-line)
	       (eq (following-char) ?})))
	(forward-char -1))
    (while (> arg 0)
      (if (re-search-forward "^}" nil t)
	  (setq arg (1- arg)
		found t)
	(setq ret nil
	      arg 0)))
    (while (< arg 0)
      (if (re-search-backward "^}" nil t)
	  (setq arg (1+ arg)
		found t)
	(setq ret nil
	      arg 0)))
    (if found
	(end-of-line))
    ret))

(defun cafeobj-outline-level ()
  (save-excursion
    (skip-chars-forward "\t ")
    (current-column)))

(defun cafeobj-inside-parens-p ()
  (condition-case ()
      (save-excursion
	(save-restriction
	  (narrow-to-region (point)
			    (progn (cafeobj-beginning-of-decl) (point)))
	  (goto-char (point-max))
	  (= (char-after (or (scan-lists (point) -1 1) (point-min))) ?\()))
    (error nil)))

(defun cafeobj-indent-command (&optional whole-exp)
  "Indent current line as CafeOBJ code, or in some cases insert a tab character.
If `cafeobj-tab-always-indent' is non-nil (the default), always indent current line.
Otherwise, indent the current line only if point is at the left margin or
in the line's indentation; otherwise insert a tab.

A numeric argument, regardless of its value, means indent rigidly all the
lines of the expression starting after point so that this line becomes
properly indented.  The relative indentation among the lines of the
expression are preserved."
  (interactive "P")
  (if whole-exp
      ;; If arg, always indent this line as CafeOBJ
      ;; and shift remaining lines of expression the same amount.
      (let ((shift-amt (cafeobj-indent-line))
	    beg end)
	(save-excursion
	  (if cafeobj-tab-always-indent
	      (beginning-of-line))
	  ;; Find beginning of following line.
	  (save-excursion
	    (forward-line 1) (setq beg (point)))
	  ;; Find first beginning-of-sexp for sexp extending past this line.
	  (while (< (point) beg)
	    (forward-sexp 1)
	    (setq end (point))
	    (skip-chars-forward " \t\n")))
	(if (> end beg)
	    (indent-code-rigidly beg end shift-amt "#")))
    (if (and (not cafeobj-tab-always-indent)
	     (save-excursion
	       (skip-chars-backward " \t")
	       (not (bolp))))
	(insert-tab)
      (cafeobj-indent-line))))

(defun cafeobj-indent-line ()
  "Indent current line as CafeOBJ code.
Return the amount the indentation changed by."
  (let ((indent (calculate-cafeobj-indent nil))
	beg shift-amt
	(case-fold-search nil)
	(pos (- (point-max) (point))))
    (beginning-of-line)
    (setq beg (point))
    (cond ((eq indent nil)
	   (setq indent (current-indentation)))
	  ((eq indent t)
	   (setq indent (current-indentation)))
	  (t
	   (skip-chars-forward " \t")
	   (if (listp indent) (setq indent (car indent)))
	   (cond ((= (following-char) ?})
		  (setq indent (- indent cafeobj-indent-level)))
		 ((= (following-char) ?{)
		  (setq indent (+ indent cafeobj-brace-offset))))))
    (skip-chars-forward " \t")
    (setq shift-amt (- indent (current-column)))
    (if (zerop shift-amt)
	(if (> (- (point-max) pos) (point))
	    (goto-char (- (point-max) pos)))
      (delete-region beg (point))
      (indent-to indent)
      ;; If initial point was within line's indentation,
      ;; position after the indentation.  Else stay at same point in text.
      (if (> (- (point-max) pos) (point))
	  (goto-char (- (point-max) pos))))
    shift-amt))

(defun calculate-cafeobj-indent (&optional parse-start)
  "Return appropriate indentation for current line as CafeOBJ code.
In usual case returns an integer: the column to indent to.
Returns nil if line starts inside a string, t if in a comment."
  (save-excursion
    (beginning-of-line)
    (let ((indent-point (point))
	  (case-fold-search nil)
	  state
	  containing-sexp)
      (if parse-start
	  (goto-char parse-start)
	(cafeobj-beginning-of-decl))
      (while (< (point) indent-point)
	(setq parse-start (point))
	(setq state (parse-partial-sexp (point) indent-point 0))
	(setq containing-sexp (car (cdr state))))
      ;;
      (cond ((or (nth 3 state) (nth 4 state))
	     ;; return nil or t if should not change this line
	     (nth 4 state))		; t if inside a comment, else nil.
	    ;; 
	    ((null containing-sexp)	; we are at top-level
	     ;; -- TOP-LEVEL------------------------------------------------
	     ;; Line is at top level.  May be module/view declaration or
	     ;; top-level commands.
	     (goto-char indent-point)	; start from original pos.
	     (skip-chars-forward " \t")
	     (cond ((= (following-char) ?{) 0)
		   ((looking-at cafeobj-top-decl-pat) 0)
		   ((looking-at cafeobj-comment-pat) (current-column))
		   (t
		    (cafeobj-backward-to-noncomment (or parse-start (point-min)))
		    ;; Look at previous line that's at column 0
		    ;; to determine whether we are in top-level decl.
		    (let ((basic-indent
			   (save-excursion
			     (re-search-backward "^[^ \^L\t\n]" nil 'move)
			     (if (and (looking-at cafeobj-top-decl-pat)
				      (not (progn
					     (condition-case nil
						 (progn
						   (search-forward "\{" parse-start)
						   (forward-list))
					       (error nil))
					     (looking-at "\}"))))
				 cafeobj-psort-indent
				 0))))
		      basic-indent))))
	    ;; NON TOPLEVEL ----------------------------------------------
	    ((and (/= (char-after containing-sexp) ?{)
		  (< (car state) 2))
	     ;; indent to just after the surrounding open.
	     (goto-char (+ 2 containing-sexp))
	     (current-column))
	    ;; WITHIN A BRACE --------------------------------------------
	    (t
	     (goto-char indent-point)
	     (if (and (not (is-cafeobj-beginning-of-statement))
		      (progn (cafeobj-backward-to-noncomment containing-sexp)
			     (not (memq (preceding-char)
					'(0 ?\, ?\} ?\{ ?\. ?\] ?\)))))
		      ;; don't treat a line with a close-brace
		      ;; as a continuation. It is probably the
		      ;; end of a block.
		      (save-excursion
			(goto-char indent-point)
			(skip-chars-forward " \t")
			(not (= (following-char) ?})))
		      )
		 ;; This line is continuation of preceding line's statement;
		 ;; indent  cafeobj-continued-statement-offset  more than the
		 ;; previous line of the statement.
		 (progn
		   (cafeobj-backward-to-start-of-continued-exp containing-sexp)
		   (+ cafeobj-continued-statement-offset (current-column)
		      (if (save-excursion (goto-char indent-point)
					  (skip-chars-forward " \t")
					  (eq (following-char) ?{))
			  cafeobj-continued-brace-offset
			  0)))
		 ;; This line starts a new statement.
		 ;; if we are looking at a comment line, leave it as is. 
		 (if (progn
		       (goto-char indent-point)
		       (skip-chars-forward " \t")
		       (looking-at cafeobj-comment-pat))
		     (current-column)
		     (progn
		       ;; Position following last unclosed open-brace.
		       (goto-char containing-sexp)
		       ;; Is line first statement after an open-brace?
		       (or
			;; If no, find that first statement and indent like it.
			(save-excursion
			  (forward-char 1)
			  (while (progn (skip-chars-forward " \t\n")
					(looking-at "--[ \t].*\\|\*\*[ \t].*"))
			    (forward-line 1))
			  ;; The first following code counts
			  ;; if it is before the line we want to indent.
			  (skip-chars-forward " \t\n")
			  (and (< (point) indent-point)
			       (- (current-column)
				  ;; If prev stmt starts with open-brace, that
				  ;; open brace was offset by cafeobj-brace-offset.
				  ;; Compensate to get the column where
				  ;; an ordinary statement would start.
				  (if (= (following-char) ?\{)
				      cafeobj-brace-offset
				      0))
			       ))
			;; If no previous statement,
			;; indent it relative to line brace is on.
			;; For open brace in column zero, don't let statement
			;; start there too.  If cafeobj-indent-level is zero,
			;; use cafeobj-brace-offset +
			;; cafeobj-continued-statement-offset instead.
			;; For open-braces not the first thing in a line,
			;; add in cafeobj-brace-imaginary-offset.
			(+ (if (and (bolp) (zerop cafeobj-indent-level))
			       (+ cafeobj-brace-offset
				  cafeobj-continued-statement-offset)
			       cafeobj-indent-level)
			   ;; Move back over whitespace before the openbrace.
			   ;; If openbrace is not first nonwhite thing on the line,
			   ;; add the cafeobj-brace-imaginary-offset.
			   (progn (skip-chars-backward " \t")
				  (if (bolp)
				      0
				      cafeobj-brace-imaginary-offset))
			   ;; If the openbrace is preceded by a parenthesized exp,
			   ;; move to the beginning of that;
			   ;; possibly a different line
			   (progn
			     (if (memq (preceding-char) '(?\) \]))
				 (forward-sexp -1))
			     ;; Get initial indentation of the line we are on.
			     (current-indentation))))))))))))

(defun is-cafeobj-beginning-of-statement ()
  (save-excursion
    (beginning-of-line)
    (skip-chars-forward " \t")
    (or (looking-at cafeobj-keyword-pat)
	(looking-at cafeobj-command-pat)
	(looking-at cafeobj-comment-pat))))

(defun cafeobj-backward-to-noncomment (lim)
  (let (stop)
    (while (not stop)
      (skip-chars-backward " \t\n\f" lim)
      (setq stop (or (<= (point) lim)
		     (save-excursion
		       (beginning-of-line)
		       (skip-chars-forward " \t")
		       (not (looking-at cafeobj-comment-pat)))))
      (or stop (beginning-of-line)))))

(defun cafeobj-backward-to-start-of-continued-exp (lim)
  (if (memq (preceding-char) '(?\) ?\" ?\]))
      (forward-sexp -1))
  (beginning-of-line)
  (if (<= (point) lim)
      (goto-char (1+ lim)))
  (skip-chars-forward " \t"))


;;; -----------------------
;;; RUN CafeOBJ Interpreter_____________________________________________________
;;; and Interact with it
;;; -----------------------
(defvar cafeobj-prompt-pattern "^[A-Za-z0-9!#$%']+> ")

(defun cafeobj-process-mode ()
  (interactive)
  (comint-mode)
  (setq major-mode 'CafeOBJ-process-mode)
  (setq mode-name "CafeOBJ process")
  (make-local-variable 'comint-prompt-regexp)
  ;;(cond (cafeobj-xemacs-p
  ;;	   (make-local-variable 'font-lock-defaults)
  ;;	   (put 'cafeobj-process-mode 'font-lock-defaults
  ;;	        '(cafeobj-font-lock-keywords)))
  ;;
  ;;   	 (t (set (make-local-variable 'font-lock-keywords)
  ;;		 cafeobj-font-lock-keywords)))
  (setq comint-prompt-regexp cafeobj-prompt-pattern)
  (setq local-abbrev-table cafeobj-mode-abbrev-table)
  (comint-read-input-ring t)
  )

(defun cafeobj-start-process (name program &optional startfile &rest switches)
  "Start a chaos process named NAME, running PROGRAM."
  (or switches
      (setq switches cafeobj-default-command-switches))
  (setq cafeobj-process-buffer (apply 'make-comint name program startfile switches))
  (setq cafeobj-process (get-buffer-process cafeobj-process-buffer))
  (save-excursion
    (set-buffer cafeobj-process-buffer)
    (cafeobj-process-mode)
    ))

(defun cafeobj (&rest ignore)
  (interactive)
  (if (and cafeobj-process
	   (eq (process-status cafeobj-process) 'run))
      (switch-to-buffer cafeobj-process-buffer)
      (progn
	(cafeobj-start-process cafeobj-default-application cafeobj-default-application)
	(switch-to-buffer-other-window cafeobj-process-buffer))))

(defun cafeobj-kill-process ()
  "Kill chaos subprocess and its buffer."
  (interactive)
  (if cafeobj-process-buffer
      (kill-buffer cafeobj-process-buffer)))

(defun cafeobj-set-cafeobj-region-start (&optional arg)
  "Set start of region for use with `cafeobj-send-cafeobj-region'."
  (interactive)
  (set-marker cafeobj-region-start (or arg (point))))

(defun cafeobj-set-cafeobj-region-end (&optional arg)
  "Set end of region for use with `cafeobj-send-cafeobj-region'."
  (interactive)
  (set-marker cafeobj-region-end (or arg (point))))

(defun cafeobj-send-line ()
  "Send current line to chaos subprocess, found in `cafeobj-process'.
If `cafeobj-process' is nil or dead, start a new process first."
  (interactive)
  (let ((start (save-excursion (beginning-of-line) (point)))
	(end (save-excursion (end-of-line) (point))))
    (or (and cafeobj-process
	     (eq (process-status cafeobj-process) 'run))
	(cafeobj-start-process cafeobj-default-application cafeobj-default-application))
    (comint-simple-send cafeobj-process (buffer-substring start end))
    (forward-line 1)
    (if cafeobj-always-show
	(display-buffer cafeobj-process-buffer))))

(defun cafeobj-send-region (start end)
  "Send region to chaos subprocess."
  (interactive "r")
  (or (and cafeobj-process
	   (comint-check-proc cafeobj-process-buffer))
      (cafeobj-start-process cafeobj-default-application cafeobj-default-application))
  (comint-simple-send cafeobj-process
		      (concat (buffer-substring start end) "\n"))
  (if cafeobj-always-show
      (display-buffer cafeobj-process-buffer)))

(defun cafeobj-send-decl ()
  "Send proc around point to chaos subprocess."
  (interactive)
  (let (beg end)
    (save-excursion
      (cafeobj-beginning-of-decl)
      (setq beg (point))
      (cafeobj-end-of-decl)
      (setq end (point)))
    (or (and cafeobj-process
	     (comint-check-proc cafeobj-process-buffer))
	(cafeobj-start-process cafeobj-default-application cafeobj-default-application))
    (comint-simple-send cafeobj-process
			(concat (buffer-substring beg end) "\n"))
    (if cafeobj-always-show
	(display-buffer cafeobj-process-buffer))))

(defun cafeobj-send-buffer ()
  "Send whole buffer to chaos subprocess."
  (interactive)
  (or (and cafeobj-process
	   (comint-check-proc cafeobj-process-buffer))
      (cafeobj-start-process cafeobj-default-application cafeobj-default-application))
  (if (buffer-modified-p)
      (comint-simple-send cafeobj-process
			  (concat
			   (buffer-substring (point-min) (point-max))
			   "\n"))
    (comint-simple-send cafeobj-process
			(concat "input "
				(buffer-file-name)
				"\n")))
  (if cafeobj-always-show
      (display-buffer cafeobj-process-buffer)))

(defun cafeobj-show-process-buffer ()
  "Make sure `cafeobj-process-buffer' is being displayed."
  (interactive)
  (display-buffer cafeobj-process-buffer))

(defun cafeobj-hide-process-buffer ()
  "Delete all windows that display `cafeobj-process-buffer'."
  (interactive)
  (delete-windows-on cafeobj-process-buffer))

;;; KB7 style commands for syntax-oriented editing of CafeOBJ constructs
;;;


(defvar cafeobj-kb7-indent-to "  "
  "tells how much to indent to, and is user settable")

(defvar cafeobj-kb7-mark-1st-field  nil
  "marking the 1st field in the current template")

(defvar cafeobj-kb7-template-markers nil 
  "this is a history of pairs of markers, the 1st marking the
beginning of the template, and the second the end")

(defun modd () (interactive)
  (beginning-of-line) (cafeobj-kb7-template-create "mod")
)
(defun mod! () (interactive)
  (beginning-of-line) (cafeobj-kb7-template-create "mod!")
)
(defun mod* () (interactive)
  (beginning-of-line) (cafeobj-kb7-template-create "mod*")
)
(defun pr () (interactive)
  (beginning-of-line) (cafeobj-kb7-template-create "protecting")
)
(defun ex () (interactive)
  (beginning-of-line) (cafeobj-kb7-template-create "extending")
)
(defun using () (interactive)
  (beginning-of-line) (cafeobj-kb7-template-create "using")
)
(defun vsort () (interactive)
  (beginning-of-line) (cafeobj-kb7-template-create "vsort")
)
(defun hsort () (interactive)
  (beginning-of-line) (cafeobj-kb7-template-create "hsort")
)
(defun op () (interactive)
  (beginning-of-line) (cafeobj-kb7-template-create "op")
)
(defun bop () (interactive)
  (beginning-of-line) (cafeobj-kb7-template-create "bop")
)
(defun var () (interactive)
  (beginning-of-line) (cafeobj-kb7-template-create "var")
)
(defun eqq () (interactive)
  (beginning-of-line) (cafeobj-kb7-template-create "eq")
)
(defun cq () (interactive)
  (beginning-of-line) (cafeobj-kb7-template-create "cq")
)
(defun beq () (interactive)
  (beginning-of-line) (cafeobj-kb7-template-create "beq")
)
(defun trans () (interactive)
  (beginning-of-line) (cafeobj-kb7-template-create "trans")
)
(defun ctrans () (interactive)
  (beginning-of-line) (cafeobj-kb7-template-create "ctrans")
)
(defun bcq () (interactive)
  (beginning-of-line) (cafeobj-kb7-template-create "bcq")
)
(defun btrans () (interactive)
  (beginning-of-line) (cafeobj-kb7-template-create "btrans")
)
(defun view () (interactive)
  (beginning-of-line) (cafeobj-kb7-template-create "view")
)
(defun make () (interactive)
  (beginning-of-line) (cafeobj-kb7-template-create "make")
)

(defun cafeobj-kb7-template-create (command)
  "constructs the template corresponding to 'command' and moves the
cursor at the beginning of the 1st field of the template. It also
marks both the beginning of the template and the position immediately
after the template"
  (let ( (keyword (cafeobj-kb7-keyword command))
         (cafeobj-kb7-template-beg (make-marker))
	 (cafeobj-kb7-template-end (make-marker))
       )
    (set-marker cafeobj-kb7-template-beg (point-marker))
    (cafeobj-kb7-intpr-schema (cafeobj-kb7-schema-create command) keyword)
    (set-marker cafeobj-kb7-template-end (- (point-marker) 1))
    (cafeobj-kb7-history-join
     (cafeobj-kb7-marker-pair-new cafeobj-kb7-template-beg cafeobj-kb7-template-end)
		      cafeobj-kb7-template-markers
    )
    (goto-char (1+ cafeobj-kb7-mark-1st-field))
))

(defun cafeobj-kb7-keyword (command)
  "gets the keyword of the respective command. this is the string from
the begining of the command to the 1st '-' " 
  (concat (cafeobj-kb7-kill-after-minus  (append command nil)))
)

(defun cafeobj-kb7-1st-identif (beg end)
  "returns the 1st identifier of the construct delimitated by beg and end"
  (let* ( (i (cafeobj-kb7-cross-blanks beg end))
	  (begining-of-identifier i)
        )
    (setq i (cafeobj-kb7-cross-identif i))
    (buffer-substring begining-of-identifier i)
))    

(defun cafeobj-kb7-kill-after-minus (list-of-int)
  "delets the rest of the string from the 1st '-' on. the string is
represented as a list of integers representing the code of the
characters of the respective string. the result is given in the same
form of a list of integers."
  (cond ( (null list-of-int)
	  nil
	)
	( (= (car list-of-int) 45)
	  nil
	)
	(t
	  (cons (car list-of-int)
		(cafeobj-kb7-kill-after-minus (cdr list-of-int)))
	)
   )
)

(defun cafeobj-kb7-schema-create (command)
  "constructs the schema for the template corresponding to 'command'"
   (cond ( (equal command "module")
           '(keyword 2 "{" nl nl "}" nl)
	 )
	 ( (equal command "mod!")
           '(keyword 2 "{" nl nl "}" nl)
	 )
	 ( (equal command "mod*")
           '(keyword 2 "{" nl nl "}" nl)
	 )
	 ( (equal command "protecting")
           '(ind keyword "(" ")" nl)
	 )
	 ( (equal command "extending")
           '(ind keyword "(" ")" nl)
	 )
	 ( (equal command "using")
           '(ind keyword "(" ")" nl)
	 )
	 ( (equal command "vsort")
	   '(ind "[" "  ]" nl)
	 )
 	 ( (equal command "hsort")
	   '(ind "*[" "  ]*" nl)
	 )
	 ( (equal command "op")
	   '(ind keyword 2 ":" 2 "->" 2 nl)
	 )
	 ( (equal command "bop")
	   '(ind keyword 2 ":" 2 "->" 2 nl)
	 )
	 ( (equal command "var")
	   '(ind keyword 2 ":" 2 nl)
	 )
	 ( (equal command "eq")
	   '(ind keyword 2 "=" 2 "." nl)
	 )
         ( (equal command "cq")
           '(ind keyword 2 "=" 2 nl ind 3 "if" 2 "." nl)
         )
	 ( (equal command "beq")
	   '(ind keyword 2 "=" 2 "." nl)
	 )
 	 ( (equal command "trans")
	   '(ind keyword 2 "=>" 2 "." nl)
	 )
	 ( (equal command "ctrans")
           '(ind keyword 2 "=>" 2 nl ind 3 "if" 2 "." nl)
	 )
	 ( (equal command "bcq")
           '(ind keyword 2 "=>" 2 nl ind 3 "if" 2 "." nl)
	 )
	 ( (equal command "btrans")
	   '(ind keyword 2 "=>" 2 "." nl)
	 )
	 ( (equal command "view")
           '(keyword 2 "from" 2 "to" 2 "is" nl nl "endv" nl)
	 )
	 ( (equal command "make")
	   '(keyword 2 "is" nl nl "endm" nl)
	 )
         (t nil)
   )
)

(defun cafeobj-kb7-intpr-schema (schema keyword)
  "interprets the template schema into code printing the respective
template. After it has done so it marks the end of the template."
  (if schema
      (progn 
      (cafeobj-kb7-intpr-item (car schema) keyword)
      (cafeobj-kb7-intpr-schema (cdr schema) keyword)
      )
  ;else
      nil
  )
)

(defun cafeobj-kb7-intpr-item (item keyword)
  "interprets an item from a template schema as printing code. It also
marks the beginning of the keyword of the template."
  (cond ( (stringp item)
          (insert item)
	  (cond ( (equal item "[")
	          (setq cafeobj-kb7-mark-1st-field (point))
	        )
		( (equal item "*[")
		  (setq cafeobj-kb7-mark-1st-field (point))
		)
		(t nil)
	  )
        )
        ( (numberp item) 
          (cafeobj-kb7-indent-nr item)
        ) 
        ( (equal item 'ind)
          (insert cafeobj-kb7-indent-to)
        )
        ( (equal item 'nl)
          (newline)
        )
        ( (equal item 'keyword)
          (insert keyword)
	  (setq cafeobj-kb7-mark-1st-field (point))
        )
        (t nil)
  )
)

(defun cafeobj-kb7-indent-nr (n)
  "inserts n blank spaces"
  (let ( (m n)
       )
  (while (/= m 0) (insert " ") (setq m (- m 1)))
))


; This section of the code also sets up a local keymode, within which the
; TAB key can be redefined.

(defconst cafeobj-kb7-keywords-for-TAB
  '("op" "ops" 
      "bop" "pred" "bops" "bpred"
      "imports" "protecting" "pr"
      "extending" "ex" "using" "us"
      "signature" "axioms" 
      "var" "vars"
      "eq" "cq" "ceq" 
      "bq" "beq" "bcq" "bceq" 
      "trans" "trns" "ctrans" "ctrns" 
      "btrans" "btrns" "bctrans" "bctrns"
      "class" "record" "attr"
      "view"
      "sort" "hsort"
      "psort" "principal-sort"
      "let" "red" "reduce" "input" "in" 
      "execute" "exec" "make"
      "apply" "start" "match"
      "parse"
      "select"
      "set"
      "show"
      "describe"
      "sh"
      "choose" "open" "close"
      "desc" "eof"
      "require" "provide"
      "mod" "mod!" "mod*" "module" "module!" "module*"
      "if" ":" "->" "=" "=>" "<" "." "[" "]" "*[" "]*" "{" "}" "(" ")")
  "OBJ keywords to be found by cafeobj-kb7-scan-forward (TAB key)")

;;; If the file is being loaded for the 1st time, cafeobj-mode-map
;;; will be nil: set it to a new keymap and define the TAB key in
;;; it. Otherwise, use the existing one.
;;;
(if cafeobj-mode-map
    ()
;else
    (setq cafeobj-mode-map (make-sparse-keymap)))
(define-key cafeobj-mode-map "\t" 'cafeobj-kb7-scan-forward)

(defun cafeobj-kb7-strings-to-re (strings)
  "converts a list of strings into a regular expression which matches
any one of these strings preceded by space or newline and followed by
space, newline, or end-of-file."
    (let ((main-re (cafeobj-kb7-strings-to-re-1 strings))
         )    
    (concat "\\(^\\| \\)\\(" main-re "\\)\\(\n\\|$\\| \\)" )
))


(defun cafeobj-kb7-strings-to-re-1 (strings)
  "converts a list of strings s1...sn into the string
<s1>\\|<s2>...\\|<sn> ."
    (mapconcat 'regexp-quote strings "\\|")
)


(defvar cafeobj-kb7-keywords-re nil
  "Regular expression that matches the keywords")

;;; If the file is being loaded for the 1st time, set cafeobj-kb7-keywords-re
;;; to the regular expression corresponding to cafeobj-kb7-keywords.
;;;
(if cafeobj-kb7-keywords-re
    ()
;else
    (setq cafeobj-kb7-keywords-re
	  (cafeobj-kb7-strings-to-re cafeobj-kb7-keywords-for-TAB))
)    

(defun cafeobj-kb7-scan-forward ()
  "searches forward for the next OBJ keyword"
  (interactive)
  (setq cafeobj-kb7-plural-position nil)
  (if (cafeobj-kb7-var/op/bop)
      (if cafeobj-kb7-plural-position
          (if (< 1 (cafeobj-kb7-sorts-count cafeobj-kb7-plural-position
					    (point)))
	      (cafeobj-kb7-pluralise-1st-keyword)
          ;else nothing
          )
      ;else
	  (cafeobj-kb7-underscores-agree-arity)
       )
  ;else nothing
    )
  (re-search-forward cafeobj-kb7-keywords-re)
)

(defvar cafeobj-kb7-beg-1st-field-current-template nil)

(defvar cafeobj-kb7-plural-position nil
  "the position of the s to be inserted for pluralisation")

(defun cafeobj-kb7-var/op/bop ()
  (let* ( (position (cafeobj-kb7-position-of-current-construct))
	  (beg (+ (length cafeobj-kb7-indent-to)
		  (cafeobj-kb7-beg-position-pair position)))
	  (end (cafeobj-kb7-end-position-pair position))
	  (keyword (cafeobj-kb7-1st-identif beg end))
	  (i (cafeobj-kb7-cross-blanks (point) end))
	)
    (cond ( (null position)
	    nil
	  )
	  ( (string-equal keyword "var")
	    (setq cafeobj-kb7-plural-position (+ beg (length keyword)))
	    (cafeobj-kb7-next-separator-is-: i)
	  )
	  ( (or (string-equal keyword "op")
		(string-equal keyword "bop"))
	    (cond ( (cafeobj-kb7-next-separator-is-: i)
		    (setq cafeobj-kb7-plural-position
			  (+ beg (length keyword)))
		    t
		  )
		  ( (cafeobj-kb7-next-separator-is--> i)
	            (setq cafeobj-kb7-beg-1st-field-current-template
		      (+ (length keyword) beg 1))
		    t
		  )
		  (t nil)
	    )
	  )
	  (t  nil)
)))

(defun cafeobj-kb7-next-separator-is-: (position)
  (and (char-equal (char-after position) 58)
       (char-equal (char-after (1+ position)) 32)
  )
)

(defun cafeobj-kb7-next-separator-is--> (position)
  (and (char-equal (char-after position) 45)
       (char-equal (char-after (1+ position)) 62)
  )
)  

(defun cafeobj-kb7-pluralise-1st-keyword ()
  "appends s to 1st keyword of current construct"
  (let ( (current-point (point))
       )
  (goto-char cafeobj-kb7-plural-position)
  (insert "s")
  (goto-char (1+ current-point))
))

(defun cafeobj-kb7-underscores-agree-arity ()
  (let* ( (underscores-count
	   (cafeobj-kb7-underscores-count
	     cafeobj-kb7-beg-1st-field-current-template))
	  (nr-of-underscores (car underscores-count))
	  (position-of-: (cdr underscores-count))
        )
    (if (/= nr-of-underscores (cafeobj-kb7-sorts-count (1+ position-of-:)
					       (point)))
	(princ "number of underscores doesnt agree with arity")
    )
))   


(defun cafeobj-kb7-cross-blanks (start end)
  "crosses a string of blanks starting with position start and up to
position end. It returns the 1st non-blank position after the string,
or end if it doesn't finish before end"
  (let ( (i start)
       )
    (while (and (< i end) (char-equal (char-after i) 32))
      (setq i (1+ i))
    )
    i
))

(defun cafeobj-kb7-cross-identif (start)
  "crosses an identifier (i.e., string of non-blank characters). It returns
the 1st blank position after the identifier."
  (let ( (i start)
       )
    (while (not (char-equal (char-after i) 32))
      (setq i (1+ i))
    )
    i
))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
(defun cafeobj-kb7-undo ()
  "if the cursor is within one of the templates in cafeobj-kb7-template-markers
then delete the corresponding text, and also delete the template from
cafeobj-kb7-template-markers." 
  (interactive)
  (let ( (current-region)
       )
    (if (= (cafeobj-kb7-history-length cafeobj-kb7-template-markers) 0)
        (princ "no template history left")
    ;else
      (setq current-region
	    (cafeobj-kb7-delete-if-satisfies
	     'cafeobj-kb7-marker-pair-surrounds-point
	      cafeobj-kb7-template-markers)
      )
      ;;; This sets current-region to the 1st marker-pair in
      ;;; cafeobj-kb7-history-markers which the cursor is inside,
      ;;; and deletes that
      ;;; marker-pair from cafeobj-kb7-template-markers.  
      ;;; It will be nil if their is no such marker-pair.
      
      (if current-region
	(delete-region (cafeobj-kb7-marker-pair-beg current-region)
		       (cafeobj-kb7-marker-pair-end current-region))
      ;else
        (princ "template not found")
      )
    )
  )
)


(defun cafeobj-kb7-underscores-count (start)
  "counts the number of underscores from start position to ` : '"
  (let ( (p start)
	 (n 0)
       )
    (while (not (char-equal (char-after p) 58))
      (if (char-equal (char-after p) 95)
	  (setq n (1+ n))
      ;else ()
      )
      (setq p (1+ p))
    )
    (cons n p)
))

(defun cafeobj-kb7-sorts-count (start end)
  "counts the number of sorts appearing in the arity of an operation
declaration or in a [sub]sort declaration. The arity lies between the marker
positions start and end, and the sorts are taken to be separated by blanks" 
  (let ( (i start)
	 (f start)
	 (sort-count 0)
       )
    (while (< i end)
      (setq f i)
      (setq i (cafeobj-kb7-cross-identif i))
      (if (< f i)
	  (setq sort-count (1+ sort-count))
      )
      (setq i (cafeobj-kb7-cross-blanks i end))
    )
    sort-count
))
	
      
  
;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
(defun cafeobj-kb7-marker-pair-new (beg end)
  "returns a new marker pair <beg,end>."
  (cons beg end)
)

(defun cafeobj-kb7-marker-pair-beg (pair)
  "returns the beginning marker from a pair."
  (car pair)
)

(defun cafeobj-kb7-marker-pair-end (pair)
  "returns the end marker from a pair."
  (cdr pair)
)

(defun cafeobj-kb7-marker-pair-surrounds-point (pair)
  "true if the cursor lies within the text represented by pair."
  (if (null pair)
      nil
  ;else
      (and (<= (marker-position (car pair)) (point) )
	   (< (point) (marker-position (cdr pair)) )
      )
  )  
)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
(defvar cafeobj-kb7-history-bound 50
  "bounds the histories. Use same bound for each at present"
)

(defun cafeobj-kb7-history-new ()
  "returns a new empty history"
  (cons 0 nil)
)

(defun cafeobj-kb7-history-length (history)
  "returns the length of history"
  (car history)
)

(defun cafeobj-kb7-history-join (item history)
  "makes item join the history. If the history is full the element at
the front leaves the history. it returns nothing but changes the
original history as a side-effect"
  (let ( (number-of-elements (car history))
	 (contents (cdr history))
       )
    (if (= number-of-elements cafeobj-kb7-history-bound)
	(progn
	  (butlast contents)
	  (setq contents (cons item contents))
	)
    ;else
        (setq contents (cons item contents))
	(setq number-of-elements (1+ number-of-elements)) 
    )
    (setcdr history contents)
    (setcar history number-of-elements)
  )
)

(defun cafeobj-kb7-delete-if-satisfies (pred history)
  "deletes elements from history which satisfy pred"
  (let ( (contents (cdr history))
	 (result)
       )
    (if (funcall pred (car contents))
	(progn
	  (setq result (car contents))
	  (setcdr history (cdr history))
	  (setcar history (- (car history) 1))
	  result
	)
    ;else
      (while (and (not (funcall pred (cadr contents)))
		  (cdr contents)
	     )
	(setq contents (cdr contents))
      )
      (if (null (cdr contents))
	  ; no element present
	  nil
      ;else
	(setq result (cadr contents))
	(setcdr contents (cddr contents))
	(setcar history (- (car history) 1))
	result
      )
    )
  )
)

(defun cafeobj-kb7-find-marker-pair (stack-of-marker-pairs)
  "finds the marker pair surrounding the point in a stack of marker pairs"  
    (cond ( (null stack-of-marker-pairs)
	    (princ "template not found")
	    nil
	  )
	  ( (cafeobj-kb7-marker-pair-surrounds-point (car stack-of-marker-pairs))
	    (car stack-of-marker-pairs)
	  )
	  (t (cafeobj-kb7-find-marker-pair (cdr stack-of-marker-pairs))
	  )
))

(defun cafeobj-kb7-position-of-current-construct ()
   (let* ( (current-template-markers
	   (cafeobj-kb7-find-marker-pair (cdr cafeobj-kb7-template-markers)))
	 )
     (if current-template-markers
	 (cons (marker-position
		(cafeobj-kb7-marker-pair-beg current-template-markers))
	       (marker-position
		(cafeobj-kb7-marker-pair-end current-template-markers))
         )
     ;else nothing
     )
))

(defun cafeobj-kb7-beg-position-pair (pair)
  (car pair)
)

(defun cafeobj-kb7-end-position-pair (pair)
  (cdr pair)
)  






; SOME USEFUL FUNCTIONS NOT AVAILABLE IN ELISP
; --------------------------------------------

(defun cddr (list)
  "usual lisp function"
  (cdr (cdr list))
)

(defun cdddr (list)
  "usual lisp function"
  (cdr (cddr list))
)

(defun cadr (list)
  "usual lisp function"
  (car (cdr list))
)

(defun caar (list)
  "usual lisp function"
  (car (car list))
)

(defun cadar (list)
  "usual lisp function"
  (car (cdr (car list)))
)

(defun caadr (list)
  "usual lisp function"
  (car (car (cdr list)))
)

(defun cadadr (list)
  "usual lisp function"
  (car (cdr (car (cdr list))))
)

(defun butlast (list)
  "removes last element in list as a side-effect, and returns nothing. 
This is apparently unavailable in Elisp" 
  (let ( (a list)
       )
    (if (and a (cdr a))
	(progn
	  (while (cddr a)
               (setq a (cdr a))
          )
          (setcdr a nil)
	)
    ;else
        nil
    )
  )
)
     

;;; Initialisations
;;; ---------------
;;;
;;; Some variables have to be set to values returned from various ADT
;;; functions. Since this can't be done until the functions are defined,
;;; which is near the end of the file, we put the initialisations right
;;; at the end, here. 
;;;
(setq cafeobj-kb7-template-markers (cafeobj-kb7-history-new))


(provide 'cafeobj-mode)

;; Local Variables:
;; folded-file: t
;; End:

;;; cafeobj-mode.el ends here


