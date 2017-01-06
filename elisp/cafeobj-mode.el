;;; cafeobj-mode.el --- CafeOBJ code editing and Interaction with
;;;                     CafeOBJ interpreter.
;;;
;;; Copyright (c) 2000-2016, Toshimi Sawada. All rights reserved.
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
;;;     (autoload 'cafeobj-mode "cafeobj-mode" "CafeOBJ mode." t)
;;;     (setq auto-mode-alist
;;;           (cons '("\\.mod$" . cafeobj-mode) auto-mode-alist))
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
;;;     (setq cafeobj-mode-map (make-sparse-keymap))
;;; and
;;;     (define-key cafeobj-mode-map <your-key> <function>)
;;; for all the functions you need.
;;;
;;; ABBREV-MODE:
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
;;;     "mod"   ->  "module"
;;;     "mod*"  ->  "module*"
;;;     "mod!"  ->  "module!"
;;;     "obj"   ->  "module!"
;;;     "th"    ->  "module*"
;;; For this, we can use `M-x edit-abbrevs' and adds the above definitions in
;;; cafeobj-abbrev-table like this:
;;;
;;; (cafeobj-mode-abbrev-table)
;;;
;;;    "mod"     0     "module"
;;;    "m*"      0     "module* "
;;;    "m!"      0     "module! "         
;;;    "obj"     0     "module!"
;;;    "th"      0     "module*"
;;;    "comm"    0     "commutative"
;;;            :
;;;            :
;;; After editting, type `C-c C-c'(M-x edit-abbrevs-redefine) to install
;;; abbrev definitions as specified. 
;;; Then use `M-x write-abbrev-file' specifying ~/.abbrev_defs to
;;; the target file name, and adds a line in my .emacs
;;; (read-abbrev-file "~/.abbrev_defs").
;;; See Emacs manual of Infos for detail.
;;;
;;; CUTOMIZABLE VARIABLES:
;;; You may want to customize the following variables, see the comment strings
;;; for the descriptions of these variables.
;;;
;;;     cafeobj-always-show
;;;     cafeobj-mode-map
;;;     cafeobj-prefix-key
;;;     cafeobj-mode-hook
;;;     cafeobj-default-application
;;;     cafeobj-default-command-switches
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
(require 'custom)
(require 'font-lock)
(require 'abbrev)
(require 'imenu)

(defgroup cafeobj nil
  "CafeOBJ code editting."
  :group 'unix
  :group 'languages)

;;; -----------------------
;;; Customizable variables _____________________________________________________
;;; -----------------------

(defcustom cafeobj-always-show t
  "*Non-nil means display cafeobj-process-buffer after sending a command."
  :type 'boolean
  :group 'cafeobj)

(defcustom cafeobj-prefix-key "\C-c"
  "Prefix for all cafeobj-mode commands."
  :type 'string
  :group 'cafeobj)

(defcustom cafeobj-mode-hook nil
  "*Hook called when CafeOBJ mode fires up."
  :type 'hook
  :group 'cafeobj)

(defcustom cafeobj-default-application "cafeobj"
  "Default Chaos dialect to run in chaos subprocess."
  :type 'string
  :group 'cafeobj)

(defcustom cafeobj-application-name "cafeobj"
  "Default name of Chaos dialect ")

(defcustom cafeobj-default-command-switches nil
  "Command switches for `cafeobj-default-application'.
Should be a list of strings which will be given to the cafeobj process when star up."
  :group 'cafeobj)

;;; simple imenu support
(defcustom cafeobj-imenu-generic-expression-alist
  '(("Modules" "^mod.* \\(\\w+\\b\\)" 1)
    ("Vars" "var.* \\(\\w+\\b\\):" 1)
    )
  "Alist of regular expressions for the imode index. 
Each element form (submenu-name regexp index).
Where submenu-name is the name of the submenu under which
items matching regexp are placed. When submenu-name is nil
the matching entries appear in the root imenu list.
Regexp idex indicates which regexp text group defines the
text entry. When the index is 0 the entire :text that matches
regexp appers."
  :type '(repeat (list (choice :tag "Submenu Name" string (const nil))
                       regexp (integer :tag "Regexp index")))
  :group 'cafeobj
  )

(add-hook 'cafeobj-mode-hook
          (lambda ()
            (setq imenu-generic-expression cafeobj-imenu-generic-expression-alist)))

;;; FACES for CafeOBJ/CafeOBJ-Process

(defgroup cafeobj-faces nil
  "CafeOBJ faces."
  :group 'cafeobj)

(defface cafeobj-comment-face-1
  '((((class color) (background dark)) (:foreground "DarkKhaki"))
    (((class color) (background light)) (:foreground "chocolate"))
    (((class grayscale) (background light))
     (:foreground "DimGray" :bold t :italic t))
    (((class grayscale) (background dark))
     (:foreground "LightGray" :bold t :italic t))
    (t (:bold t)))
  "Face used to highlight comments."
  :group 'cafeobj-faces)

(defface cafeobj-comment-face-2
  '((((class color) (background dark)) (:foreground "honeydew3"))
    (((class color) (background light)) (:foreground "blue4"))
    (((class grayscale) (background light))
     (:foreground "DimGray" :bold t :italic t))
    (((class grayscale) (background dark))
     (:foreground "LightGray" :bold t :italic t))
    (t (:bold t)))
  "Face used to highlight comments."
  :group 'cafeobj-faces)

(defface cafeobj-string-face
  '((((class color) (background dark)) (:foreground "goldenrod"))
    (((class color) (background light)) (:foreground "green4"))
    (((class grayscale) (background light)) (:foreground "DimGray" :italic t))
    (((class grayscale) (background dark)) (:foreground "LightGray" :italic t))
    (t (:bold t)))
  "CafeOBJ face used to highlight strings."
  :group 'cafeobj-faces)

(defface cafeobj-string-face-2
  '((((class color) (background dark)) (:foreground "dark khaki"))
    (((class color) (background light)) (:foreground "green4"))
    (t (:bold t)))
  "CafeOBJ face used to highlight strings."
  :group 'cafeobj-faces)

(defface cafeobj-keyword-face
  '((((class color) (background dark)) (:foreground "DarkSeaGreen3"))
    (((class color) (background light)) (:foreground "red4"))
    (((class grayscale) (background light)) (:foreground "LightGray" :bold t))
    (((class grayscale) (background dark)) (:foreground "DimGray" :bold t))
    (t (:bold t)))
  "CafeOBJ face used to highlight keywords."
  :group 'cafeobj-faces)

(defface cafeobj-decl-keyword-face
  '((((class color) (background dark))
     (:foreground "LightGoldenrod3" :background "DimGray"))
    (((class color) (background light))
     (:foreground "LightGoldenrod3" :background "DimGray"))
    (((class grayscale) (background light)) (:foreground "LightGray":bold t))
    (((class grayscale) (background dark)) (:foreground "DimGray" :bold t))
    (t (:bold t)))
  "CafeOBJ face used to highlight keywords."
  :group 'cafeobj-faces)

(defface cafeobj-command-name-face
  '((((class color) (background dark)) (:foreground "LightSkyBlue1"))
    (((class color) (background light)) (:foreground "brown4"))
    (t (:bold t :underline t)))
  "CafeOBJ face used to highlight command names."
  :group 'cafeobj-faces)

(defface cafeobj-message-1-face
  '((((class color) (background dark))
     (:foreground "LightGoldenrod1" :background "DimGray"))
    (((class color) (background light))
     (:foreground "LightGoldenrod1" :background "DimGray"))
    (((class grayscale) (background light))
     (:foreground "Gray90" :bold t :italic t))
    (((class grayscale) (background dark))
     (:foreground "DimGray" :bold t :italic t))
    (t (:underline t)))
  "CafeOBJ face used to highlight message type 1."
  :group 'cafeobj-faces)

(defface cafeobj-message-2-face
  '((((class color) (background dark)) (:foreground "LightGoldenrod3"))
    (((class color) (background light)) (:foreground "steelblue"))
    (((class grayscale) (background light)) (:foreground "Gray90" :bold t))
    (((class grayscale) (background dark)) (:foreground "DimGray" :bold t))
    (t (:bold t)))
  "CafeOBJ face used to highlight message type 2."
  :group 'cafeobj-faces)

(defface cafeobj-message-3-face
    '((((class color) (background dark))
       (:foreground "IndianRed1"))
      (((class color) (background light)) (:foreground "IndianRed3"))
      (((class grayscale) (background light)) (:foreground "Gray90" :bold t))
      (((class grayscale) (background dark)) (:foreground "DimGray" :bold t))
      (t (:bold t)))
  "CafeOBJ face used to hightliht message type 3."
  :group 'cafeobj-face)


;;; INDENTATION CONTROL

(defcustom cafeobj-indent-level 2
  "*Indentation of CafeOBJ statements with respect to containing block."
  :type 'integer
  :group 'cafeobj)

(defcustom cafeobj-brace-imaginary-offset 0
  "*Imagined indentation of a CafeOBJ open brace that actually follows a statement."
  :type 'integer
  :group 'cafeobj)

(defcustom cafeobj-brace-offset 0
  "*Extra indentation for braces, compared with other text in same context."
  :type 'integer
  :group 'cafeobj)

(defcustom cafeobj-psort-indent 5
  "*Indentation level of principal-sort declaration of CafeOBJ."
  :type 'integer
  :group 'cafeobj)

(defcustom cafeobj-continued-statement-offset 2
  "*Extra indent for lines not starting new statements."
  :type 'integer
  :group 'cafeobj)

(defcustom cafeobj-continued-brace-offset 0
  "*Extra indent for substatements that start with open-braces.
This is in addition to cafeobj-continued-statement-offset."
  :type 'integer
  :group 'cafeobj)

;;; ---------------------------------
;;; globals for internal use only....
;;; ---------------------------------

(defvar cafeobj-mode-map nil
  "Keymap used with CafeOBJ editting mode.")

(defvar cafeobj-process nil
  "The active CafeOBJ subprocess corresponding to current buffer.")

(defvar cafeobj-process-buffer nil
  "Buffer used for communication with CafeOBJ subprocess for current buffer.")

(defvar cafeobj-region-start (make-marker)
  "Start of special region for CafeOBJ communication.")

(defvar cafeobj-region-end (make-marker)
  "End of special region for CafeOBJ communication.")

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

(defconst cafeobj-comment-pat-1 "[ \t]*\\*\\*>?[ \t]+.*$")
(defconst cafeobj-comment-pat-2 "[ \t]*-->?[ \t]+.*$")
(defconst cafeobj-comment-pat-3 "[ \t]*\\*\\*?[ \t]+.*$")
(defconst cafeobj-comment-pat-4 "[ \t]*--?[ \t]+.*$")

(defun looking-at-cafeobj-comment-pat ()
  (or (looking-at cafeobj-comment-pat-1)
      (looking-at cafeobj-comment-pat-2)
      (looking-at cafeobj-comment-pat-3)
      (looking-at cafeobj-comment-pat-4)))

(defconst cafeobj-keywords-1
    '("op"
      "ops"
      "sort"
      "hsort"
      "bop"
      "pred"
      "bops"
      "#define"
      "bpred"
      "var"
      "vars"
      "eq"
      "cq"
      "ceq" 
      "bq"
      "beq"
      "bcq"
      "bceq" 
      "trans"
      "trns"
      "rl"
      "crl"
      "ctrans"
      "ctrns" 
      "btrans"
      "btrns"
      "bctrans"
      "bctrns"
      "class"
      "record"
      "attr"
      "view"
      "sort"
      "hsort"
      "psort"
      "principal-sort"
      "ax"
      "fax"
      "protecting"
      "pr"
      "extending"
      "ex"
      "using"
      "us"
      "including"
      "inc"
      "goal"
      )
  "keywords appearing inside module declaration or view declaration."
  )

(defconst cafeobj-keyword-pat-1
  (concat "^[ \t]*\\(" (regexp-opt cafeobj-keywords-1) "\\)\\>"))

(defconst cafeobj-keywords-2
    '("imports"
      "signature"
      "axioms" 
      )
  "keywords 2."
  )

(defconst cafeobj-keyword-pat-2
  (if cafeobj-xemacs-p
      ;; (concat "^[ \t]*" (regexp-opt cafeobj-keywords-2 t t) "\\>")
      (concat "^[ \t]*" (regexp-opt cafeobj-keywords-2 ) "\\>")
    (concat "^[ \t]*\\("
            (regexp-opt cafeobj-keywords-2)
            "\\)\\>")))


(defconst cafeobj-keyword-pat-3
    "\\(^[ \t]*\\*?\\[ \\| \\]\\*?\\)")

(defconst cafeobj-keyword-pat-4
  (concat "[ \t]*" (regexp-opt '("sort"
                                 "hsort"
                                 "bop"
                                 "op"
                                 "if"
                                 "then"
                                 "else"
                                 "fi"
                                 "."))
          "\\>"))

(defun looking-at-cafeobj-keyword-pat ()
  (or (looking-at cafeobj-keyword-pat-1)
      (looking-at cafeobj-keyword-pat-2)
      (looking-at cafeobj-keyword-pat-3)
      (looking-at cafeobj-keyword-pat-4)))

(defconst cafeobj-commands-1
    '("let"
      "red"
      "reduce"
      "bred"
      "breduce"
      "cbred"
      "input"
      "in" 
      "execute"
      "exec"
      "make"
      "apply"
      "start"
      "match"
      "unify"
      "parse"
      "select"
      "set"
      "show"
      "describe"
      "sh"
      "tram"
      "check"
      "choose"
      "open"
      "close"
      "desc"
      "eof"
      "protect"
      "unprotect"
      "require"
      "provide"
      "resolve"
      "full"
      "reset"
      "option"
      "db"
      "sos"
      "passive"
      "save-option"
      "sigmatch"
      "list"
      "flag"
      "param"
      "lex"
      "name"
      "names"
      "look"
      "inspect"
      "inspect-term"
      ":goal"
      ":apply"
      ":auto"
      ":ind"
      ":init"
      ":imp"
      ":cp"
      ":ctf"
      ":ctf-"
      ":csp"
      ":csp-"
      ":show"
      ":sh"
      ":describe"
      ":desc"
      ":verbose"
      ":backward"
      ":equation"
      ":rule"
      ":select"
      ":order"
      ":use"
      ":embed"
      ":red"
      ":define"
      ":set"
      )
  "CafeOBJ top-level commands")


(defconst cafeobj-command-pat-1
    (concat "^[ \t]*\\(" (regexp-opt cafeobj-commands-1) "\\)\\>"))

(defun looking-at-cafeobj-command-pat ()
  (looking-at cafeobj-command-pat-1))

(defconst cafeobj-top-keywords
    (append cafeobj-keywords-1 cafeobj-commands-1)
  "CafeOBJ keyowrds may apper at top-level.")

(defun looking-at-cafeobj-top-keywords ()
  (looking-at cafeobj-top-keywords))

(defconst cafeobj-top-key-pat
    (concat "^\\<\\("
            (regexp-opt cafeobj-top-keywords)
            "\\)\\>"))

(defconst cafeobj-top-decl-pat
    (concat "^[ \t]*\\("
            "module\\|module\\*\\|mod\\*\\|module\\|mod\\|module!\\|mod!\\|view\\|hwd:mod!\\|sys:mod!"
            "\\)\\>"))

(defun looking-at-cafeobj-top-decl ()
  (looking-at cafeobj-top-decl-pat))

(defconst cafeobj-block-start-pat
    (concat "[ \t]*"
            (regexp-opt '("signature" "axioms" "imports" "record" "class")
                        t)
            "\\>"))

(defun looking-at-cafeobj-block-start-pat ()
  (looking-at cafeobj-block-start-pat))
       
(defun looking-at-cafeobj-module-decl ()
  (looking-at (concat "^\\<\\("
                      (regexp-opt '("module" "mod" "module*" "mod*"
                                    "module!" "mod!"))
                      "\\)\\>")))

(defun looking-at-cafeobj-view-decl ()
  (looking-at "^\\<view\\>"))

;;;----------
;;; FONT-LOCK___________________________________________________________________
;;;----------

(defun get-cafeobj-face (name) (identity name))

(defvar cafeobj-font-lock-keywords nil
  "Expressions to highlight in CafeOBJ mode.")

(setq cafeobj-font-lock-keywords
      (list
       ;; comments
       (list cafeobj-comment-pat-1 0 'cafeobj-comment-face-1 nil)
       (list cafeobj-comment-pat-2 0 'cafeobj-comment-face-2 nil)
       ;; keywords
       (cons cafeobj-keyword-pat-1  'cafeobj-keyword-face)
       (list cafeobj-keyword-pat-2 1 'cafeobj-decl-keyword-face)
       (cons cafeobj-keyword-pat-3  'cafeobj-keyword-face)
       ;; commands
       (cons cafeobj-command-pat-1 'cafeobj-command-name-face)
       ;; module/view
       (list cafeobj-top-decl-pat 1 'cafeobj-decl-keyword-face)
       ;; declaration appering at the top level. 
       (cons cafeobj-top-key-pat 'cafeobj-keyword-face)
       ))

(put 'cafeobj-mode 'font-lock-defaults '(cafeobj-font-lock-keywords t))

;;; -------------
;;; MENU SUPPORTS_______________________________________________________________
;;; -------------

;; For XEmacs 
(defvar cafeobj-mode-popup-menu nil)
(defvar cafeobj-mode-menubar-menu nil)

;; For FSF19
(defvar cafeobj-mode-menu nil
  "Keymap for cafeobj-mode's menu.")

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
                         ["Comment Out Region"  comment-region  (region-exists-p)]
                         ["Indent Region"       indent-region   (region-exists-p)]
                         ["Indent Line"         cafeobj-indent-line t]
                         ["Beginning of Declaration"
                          cafeobj-beginning-of-decl t]
                         )))
       (setq cafeobj-mode-menubar-menu
             (purecopy (cons "CafeOBJ" (cdr cafeobj-mode-popup-menu)))))
      (t ;; 
       (setq cafeobj-mode-menu (make-sparse-keymap "CafeOBJ"))
       (define-key cafeobj-mode-menu [cafeobj-send-line]
         '("Evaluate Current Line" . cafeobj-send-line))
       (define-key cafeobj-mode-menu [cafeobj-send-region]
         '("Evaluate Cafeobj-Region" . cafeobj-send-region))
       (define-key cafeobj-mode-menu [cafeobj-send-proc]
         '("Evaluate This Declaration" . cafeobj-send-decl))
       (define-key cafeobj-mode-menu [cafeobj-send-buffer]
         '("Send Buffer" . cafeobj-send-buffer))
       (define-key cafeobj-mode-menu [cafeobj-beginning-of-decl]
         '("Beginning Of Proc" . cafeobj-beginning-of-decl))
       (define-key cafeobj-mode-menu [comment-region]
         '("Comment Out Region" . comment-region))
       (define-key cafeobj-mode-menu [indent-region]
         '("Indent Region" . indent-region))
       (define-key cafeobj-mode-menu [cafeobj-indent-line]
         '("Indent Line" . cafeobj-indent-line))
       (define-key cafeobj-mode-menu [cafeobj-beginning-of-decl]
         '("Beginning of Declaration" . cafeobj-beginning-of-decl))
       ))

;;; ------------
;;; CafeOBJ Mode________________________________________________________________
;;; ------------

(defvar cafeobj-mode-abbrev-table nil
  "Abbrev table in use in CafeOBJ mode.")

;;; se use extended abbriv 
(autoload 'expand-abbrev-hook "expand")

;;; some default abbreviations defined here
;;; 
'(if cafeobj-mode-abbrev-table
    nil
  (define-abbrev-table 'cafeobj-mode-abbrev-table
    '(;; top level declaration
      ("mod" ["module  {\n\n}\n" 5 () nil] expand-abbrev-hook 0)
      ("pmod" ["module  () {\n\n}\n" 8 () nil] expand-abbrev-hook 0)
      ("vw" ["view  {\n\n}\n" 5 () nil] expand-abbrev-hook 0)
      ("mk" ["make  ()" 3 () nil] expand-abbrev-hook 0)
      ;; module constructs
      ("ps" "pricipal-sort" nil 0)
      ;; imports
      ("imp" ["imports {\n\n}\n" 3 () nil] expand-abbrev-hook 0)
      ("pr" ["protecting()" 1 () nil]  expand-abbrev-hook 0)
      ("pa" ["protecting as  ()" 3 () nil] expand-abbrev-hook 0)
      ("ex" ["extending()" 1 () nil] expand-abbrev-hook 0)
      ("ea" ["extending as ()" 2 () nil] expand-abbrev-hook 0)
      ("us" ["using()" 1 () nil] expand-abbrev-hook 0)
      ("ua" ["using as ()" 2 () nil] expand-abbrev-hook 0)
      ("inc" ["including()" 1 () nil] expand-abbrev-hook 0)
      ("ias" ["including as ()" 2 () nil] expand-abbrev-hook 0)
      ;; signature
      ("sig" ["signature {\n\n}\n" 3 () nil] expand-abbrev-hook 0)
      ;; sort declarations
      ("[" ["[]" 1 () nil] expand-abbrev-hook 0)
      ("*[" ["*[]*" 2 () nil] expand-abbrev-hook 0)
      ;; operator declaration
      ("ope" ["op  :  ->   ." 10 () nil] expand-abbrev-hook 0)
      ("opt" ["op  :  ->  {} ." 12 () nil] expand-abbrev-hook 0)
      ("ops" ["ops  :  ->  ." 9 () nil] expand-abbrev-hook 0)
      ("pred" ["pred  :  ." 4 () nil] expand-abbrev-hook 0)
      ;; operator attributes
      ("str" ["strat: ()" 1 () nil] expand-abbrev-hook 0)
      ("ctr" "ctor" nil 0)
      ("ra" "r-assoc" nil 0)
      ("la" "l-assoc" nil 0)
      ("pre" "prec:" nil 0)
      ("ass" "assoc" nil 0)
      ("com" "comm" nil 0)
      ;; axiom
      ("axi" ["axioms {\n\n}\n" 3 () nil] expand-abbrev-hook 0)
      ("bt" ["btrans  =>   ." 7 () nil] expand-abbrev-hook 0)
      ("bct"["bctrans  =>  if  ."  10 () nil] expand-abbrev-hook 0)
      ("ctr" ["ctrans  =>  if  ." 10 () nil] expand-abbrev-hook 0)
      ("tr" ["trans  =>   ." 7 () nil] expand-abbrev-hook 0)
      ("eq" ["eq  =    ." 7 () nil] expand-abbrev-hook 0)
      ("cq" ["ceq  =   if  ." 10 () nil] expand-abbrev-hook 0)
      ("bq" ["beq  =   ." 7 () nil] expand-abbrev-hook 0)
      ("bcq" ["bceq  =   if  ." 10 () nil] expand-abbrev-hook 0)
      ("var" ["var  : " 3 () nil] expand-abbrev-hook 0)
      ("vars" ["vars  : " 3 () nil] expand-abbrev-hook 0)
      ;; commands   
      ("ch" "check" nil 0)
      ("comp" "compatibility " nil 0)
      ("reg" "regularity " nil 0)
      ("red" ["reduce  ." 2 () nil] expand-abbrev-hook 0)
      ("rin" ["reduce in  :  ." 5 () nil] expand-abbrev-hook 0)
      ("exe" ["execute  ." 2 () nil] expand-abbrev-hook 0)
      ("ein" ["execute in   :  ." 5 () nil] expand-abbrev-hook 0)
      ("par" ["parse  ." 2 () nil] expand-abbrev-hook 0)
      ("parse" ["parse  ." 2 () nil] expand-abbrev-hook 0)
      ("pin" ["parse in  :  ." 5 () nil] expand-abbrev-hook 0)
      ("sh" "show" nil 0)
      ("des" "describe " nil 0)
      ("regu" "regualize " nil 0)
      ("verb" "verbose" nil 0)
      ("sw" "switch" nil 0)
      ("sws" "switches" nil 0)
      ("req" "require" nil 0)
      ("prov" "provide" nil 0)
      ("sel" ["select  ." 2 () nil] expand-abbrev-hook 0)
      ;; CITP
      (":goal" [":goal {}" 1 () nil] expand-abbrev-hook 0)
      (":go"  [":goal {}" 1 () nil] expand-abbrev-hook 0)
      (":apply" [":apply ()" 1 () nil] expand-abbrev-hook 0)
      (":app" [":apply ()" 1 () nil] expand-abbrev-hook 0)
      (":ind" [":ind on ()" 1 () nil] expand-abbrev-hook 0)
      (":ini" [":init () by { ;}" 9 () nil]  expand-abbrev-hook 0)
      (":inil" [":init [] by { ;}" 9 () nil] expand-abbrev-hook 0)
      (":cp" [":cp () >< ()" 7 () nil] expand-abbrev-hook 0)
      (":cpl" [":cp [] >< []" 7 () nil] expand-abbrev-hook 0)
      (":eq" ":equation" nil 0)
      (":rl" ":rule" nil 0)
      (":bk" ":backward" nil 0)
      (":vb" ":verbose" nil 0)
      (":norm" ":normalize" nil 0)
      ;; (":ctf" [":ctf{}" 1 () nil] expand-abbrev-hook 0)
      (":csp" [":csp{}" 1 () nil] expand-abbrev-hook 0)
      (":sh" ":show" nil 0)
      (":des" ":describe" nil 0)
      ))
  )


(defvar cafeobj-mode-syntax-table nil
  "Syntax table in use in cafeobj-mode buffers.")

(if cafeobj-mode-syntax-table
    ()
  (setq cafeobj-mode-syntax-table (make-syntax-table))
  (mapc (function
         (lambda (x) (modify-syntax-entry
                      (car x) (cdr x) cafeobj-mode-syntax-table)))
        '((?\( . "()" ) ( ?\) . ")(" )
          ;; ( ?\[ . "(]" ) ( ?\] . ")[" )
          (?\{ . "(}" ) ( ?\} . "){" )
          (?\[ . "w") (?\] . "w")
          (?\* . "w")
          ;; underscore etc. is word class
          ( ?\_ . "w" )
          ( ?\# . "w" )
          ( ?\! . "w" )
          ( ?\$ . "w" )
          ( ?\% . "w" )
          ( ?\: . "w")
          ( ?\" . "\"" )        ; double quote is string quote too
          ( ?\n . ">"))
        ))
(defvar mode-popup-menu) ;only for XEmacs

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
          (cons "CafeOBJ" cafeobj-mode-menu))))
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
    (make-local-variable 'font-lock-defaults)
    (setq font-lock-defaults '(cafeobj-font-lock-keywords t))
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
            (set (make-local-variable 'cafeobj-application-name)
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
                    (set (make-local-variable 'cafeobj-application-name)
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
    ;; (if (and (featurep 'menubar)
    ;;       current-menubar)
    ;;  (progn
    ;;    ;; make a local copy of the menubar, so our modes don't
    ;;    ;; change the global menubar
    ;;    (set-buffer-menubar current-menubar)
    ;;    (add-submenu nil cafeobj-mode-menubar-menu)))
    ;;
    (run-hooks 'cafeobj-mode-hook)))

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
    (define-key map "l" 'cafeobj-send-line)
    (define-key map "e" 'cafeobj-send-decl)
    (define-key map "r" 'cafeobj-send-region)
    (define-key map "b" 'cafeobj-send-buffer)
    (define-key map "[" 'cafeobj-beginning-of-decl)
    (define-key map "]" 'cafeobj-end-of-decl)
    (define-key map "q" 'cafeobj-kill-process)
    (define-key map "s" 'cafeobj-show-process-buffer)
    (define-key map "h" 'cafeobj-hide-process-buffer)
    ;;
    (if cafeobj-prefix-key
        (define-key cafeobj-mode-map cafeobj-prefix-key map))
    ))

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
          ;; (insert last-command-char)
          (insert last-command-event)
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
             (looking-at-cafeobj-top-decl))
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
             (nth 4 state))             ; t if inside a comment, else nil.
            ;; 
            ((null containing-sexp)     ; we are at top-level
             ;; -- TOP-LEVEL------------------------------------------------
             ;; Line is at top level.  May be module/view declaration or
             ;; top-level commands.
             (goto-char indent-point)   ; start from original pos.
             (skip-chars-forward " \t")
             (cond ((= (following-char) ?{) 0)
                   ((looking-at-cafeobj-top-decl) 0)
                   ((looking-at-cafeobj-comment-pat) (current-column))
                   (t
                    (cafeobj-backward-to-noncomment (or parse-start (point-min)))
                    ;; Look at previous line that's at column 0
                    ;; to determine whether we are in top-level decl.
                    (let ((basic-indent
                           (save-excursion
                             (re-search-backward "^[^ \^L\t\n]" nil 'move)
                             (if (and (looking-at-cafeobj-top-decl)
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
                       (looking-at-cafeobj-comment-pat))
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
    ;; (skip-chars-forward " \t")
    (or (looking-at-cafeobj-keyword-pat)
        (looking-at-cafeobj-command-pat))))

(defun cafeobj-backward-to-noncomment (lim)
  (let (stop)
    (while (not stop)
      (skip-chars-backward " \t\n\f" lim)
      (setq stop (or (<= (point) lim)
                     (save-excursion
                       (beginning-of-line)
                       (skip-chars-forward " \t")
                       (not (looking-at-cafeobj-comment-pat)))))
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

(defgroup cafeobj-process nil
  "Running CafeOBJ from within Emacs buffers"
  :group 'processes
  :group 'unix)

(defgroup cafeobj-directories nil
  "Directory support in CafeOBJ process mode"
  :group 'cafeobj-process)

(defgroup cafeobj-process-faces nil
  "Faces in CafeOBJ buffers"
  :group 'cafeobj-process)

(defcustom cafeobj-completion-fignore nil
  "*List of suffixes to be disregarded during file/command completion.
This variable is used to initialize `comint-completion-fignore' in the 
CafeOBJ process buffer.  The default is nil.

This is a fine thing to set in your `.emacs' file."
  :type '(repeat (string :tag "Suffix"))
  :group 'cafeobj-process)

(defvar cafeobj-delimiter-argument-list nil ;'(?\| ?& ?< ?> ?\( ?\) ?\;
  "List of characters to recognise as separate arguments.
This variable is used to initialize `comint-delimiter-argument-list' in the
CafeOBJ buffer.

This is a fine thing to set in your `.emacs' file.")

(defvar cafeobj-file-name-chars
  (if (memq system-type '(ms-dos windows-nt))
      "~/A-Za-z0-9_^$!#%&{}@`'.()-"
    "~/A-Za-z0-9+@:_.$#%,={}-")
  "String of characters valid in a file name.
This variable is used to initialize `comint-file-name-chars' in the
CafeOBJ buffer.  The value may depend on the operating system.

This is a fine thing to set in your `.emacs' file.")

(defvar cafeobj-file-name-quote-list
  (if (memq system-type '(ms-dos windows-nt))
      nil
    (append cafeobj-delimiter-argument-list '(?\  ?\* ?\! ?\" ?\' ?\`)))
  "List of characters to quote when in a file name.
This variable is used to initialize `comint-file-name-quote-list' in the
shell buffer.  The value may depend on the operating system or shell.

This is a fine thing to set in your `.emacs' file.")

(defvar cafeobj-dynamic-complete-functions
  '(comint-replace-by-expanded-history
    cafeobj-dynamic-complete-environment-variable
    cafeobj-dynamic-complete-command
    cafeobj-replace-by-expanded-directory
    cafeobj-dynamic-complete-filename
    comint-dynamic-complete-filename)
  "List of functions called to perform completion.
This variable is used to initialise `comint-dynamic-complete-functions' in the
CafeOBJ process buffer.

This is a fine thing to set in your `.emacs' file.")

(defcustom cafeobj-command-regexp "[^;&|\n]+"
  "*Regexp to match a single command within a pipeline.
This is used for directory tracking and does not do a perfect job."
  :type 'regexp
  :group 'cafeobj-process)

(defcustom cafeobj-pushd-regexp "pushd"
  "*Regexp to match subshell commands equivalent to pushd."
  :type 'regexp
  :group 'cafeobj-directories)

(defcustom cafeobj-popd-regexp "popd"
  "*Regexp to match CafeOBJ commands equivalent to popd."
  :type 'regexp
  :group 'cafeobj-directories)

(defcustom cafeobj-pushd-tohome nil
  "*If non-nil, make pushd with no arg behave as \"pushd ~\" (like cd)."
  :type 'boolean
  :group 'cafeobj-directories)

(defcustom cafeobj-pushd-dextract nil
  "*If non-nil, make \"pushd +n\" pop the nth dir to the stack top."
  :type 'boolean
  :group 'cafeobj-directories)

(defcustom cafeobj-pushd-dunique nil
  "*If non-nil, make pushd only add unique directories to the stack."
  :type 'boolean
  :group 'cafeobj-directories)

(defcustom cafeobj-chdrive-regexp
  (if (memq system-type '(ms-dos windows-nt)) 
      ; NetWare allows the five chars between upper and lower alphabetics.
      "[]a-zA-Z^_`\\[\\\\]:"
    nil)
  "*If non-nil, is regexp used to track drive changes."
  :type '(choice regexp
                 (const nil))
  :group 'cafeobj-directories)

(defcustom cafeobj-cd-regexp "cd"
  "*Regexp to match CafeOBJ commands equivalent to cd."
  :type 'regexp
  :group 'cafeobj-directories)

(defcustom cafeobj-input-autoexpand 'history
  "*If non-nil, expand input command history references on completion.
This mirrors the optional behavior of tcsh (its autoexpand and histlit).

If the value is `input', then the expansion is seen on input.
If the value is `history', then the expansion is only when inserting
into the buffer's input ring.  See also `comint-magic-space' and
`comint-dynamic-complete'.

This variable supplies a default for `comint-input-autoexpand',
for CafeOBJ process mode only."
  :type '(choice (const nil) (const input) (const history))
  :type 'cafeobj)

(defvar cafeobj-dirstack nil
  "List of directories saved by pushd in this buffer's CafeOBJ.
Thus, this does not include the CafeOBJ's current directory.")

(defvar cafeobj-dirstack-query nil)

(defvar cafeobj-dirtrackp t
  "Non-nil in a CafeOBJ buffer means directory tracking is enabled.")

(defvar cafeobj-last-dir nil
  "Keep track of last directory.")

(defvar cafeobj-process-mode-map nil)

(cond ((not cafeobj-process-mode-map)
       (setq cafeobj-process-mode-map
             (nconc (make-sparse-keymap) comint-mode-map))
       (define-key cafeobj-process-mode-map
         "\C-c\C-f" 'cafeobj-forward-command)
       (define-key cafeobj-process-mode-map
         "\C-c\C-b" 'cafeobj-backward-command)
       (define-key cafeobj-process-mode-map
         "\t" 'comint-dynamic-complete)
       (define-key cafeobj-process-mode-map
         "\M-?"  'comint-dynamic-list-filename-completions)
       (define-key cafeobj-process-mode-map
         "\C-c\C-g" 'cafeobj-put-esc-esc)
       (define-key cafeobj-process-mode-map [menu-bar completion]
         (cons "Complete"
               (copy-keymap (lookup-key comint-mode-map [menu-bar completion]))))
       (define-key-after (lookup-key cafeobj-process-mode-map
                                     [menu-bar completion])
         [complete-env-variable] '("Complete Env. Variable Name" .
                                   cafeobj-dynamic-complete-environment-variable)
         'complete-file)
       (define-key-after (lookup-key cafeobj-process-mode-map [menu-bar completion])
         [expand-directory] '("Expand Directory Reference" .
                              cafeobj-replace-by-expanded-directory)
         'complete-expand)
       (unless (featurep 'infodock)
         (define-key cafeobj-process-mode-map "\M-\C-m" 'cafeobj-resync-dirs))
       ))

(defcustom cafeobj-process-mode-hook nil
  "*Hook for customising CafeOBJ process mode."
  :type 'hook
  :group 'cafeobj-process)

;;; FONT-LOCKING

(defface cafeobj-error-face
    '((((class color) (background dark)) 
       (:foreground "Red3" :background "DimGray"))
      (((class color) (background light))
       (:foreground "Red3" :background "DimGray"))
      (((class grayscale) (background light))
       (:foreground "LightGray" :bold t :underline t))
      (((class grayscale) (background dark))
       (:foreground "Gray50" :bold t :underline t)))
  "CafeOBJ face used to highlight error messages."
  :group 'cafeobj-faces)

(defface cafeobj-warning-face
  '((((class color) (background dark))
     (:foreground "yellow3" :background "DimGray"))
    (((class color) (background light)) 
     (:foreground "yellow3" :background "DimGray"))
    (t (:inverse-video t :bold t)))
  "Font Lock mode face used to highlight warnings."
  :group 'cafeobj-faces)

(defface cafeobj-pignose-keyword-face
  '((((class color) (background dark)) (:foreground "steelblue1"))
    (((class color) (background light)) (:foreground "blue3"))
    (t (:underline t)))
  "CafeOBJ face used to highlight keywords of PigNose."
  :group 'cafeobj-faces)

(defcustom cafeobj-prompt-face 'cafeobj-prompt-face
  "Face for shell prompts."
  :type 'face
  :group 'cafeobj-process-faces)

(defcustom cafeobj-process-keyword-face 'cafeobj-process-keyword-face
  "Face for CafeOBJ keywords."
  :type 'face
  :group 'cafeobj-process-faces)

(defcustom cafeobj-option-face 'cafeobj-option-face
  "Face for command line options."
  :type 'face
  :group 'cafeobj-process-faces)

(defcustom cafeobj-output-face 'cafeobj-output-face
  "Face for generic CafeOBJ output."
  :type 'face
  :group 'cafeobj-process-faces)


(make-face cafeobj-prompt-face)
(make-face cafeobj-process-keyword-face)
(make-face cafeobj-option-face)

(defun cafeobj-process-font-lock-mode-hook ()
  (or (face-differs-from-default-p cafeobj-prompt-face)
      (copy-face 'cafeobj-comment-face-2 cafeobj-prompt-face))
  (or (face-differs-from-default-p cafeobj-process-keyword-face)
      (copy-face 'cafeobj-comment-face-2 cafeobj-process-keyword-face))
  (or (face-differs-from-default-p cafeobj-option-face)
      (copy-face 'cafeobj-comment-face-2 cafeobj-option-face))
  ;; (or (face-differs-from-default-p cafeobj-error-face)
  ;;     (copy-face 'red cafeobj-error-face))

  ;; we only need to do this once
  (remove-hook 'font-lock-mode-hook 'cafeobj-process-font-lock-mode-hook))

(add-hook 'font-lock-mode-hook 'cafeobj-process-font-lock-mode-hook)

(defvar cafeobj-process-font-lock-keywords nil)

(progn
  (setq cafeobj-process-font-lock-keywords
    (append
     (list '(eval . (cons cafeobj-prompt-pattern
                     cafeobj-prompt-face))
           '("\\[Error\\]:" . cafeobj-error-face)
           '("\\[Warning\\]:" . cafeobj-warning-face)
           '("^\\[Properties .*$" . cafeobj-process-keyword-face)
           '("^\\[selected .*$" . cafeobj-comment-face-2)
           '("^\\* kept .*$" . cafeobj-comment-face-1)
           '("^\\*\\* success$" . cafeobj-message-3-face)
           '("^\\*\\* fail$" . cafeobj-message-3-face)
           '("^\\*\\* found .*$" . cafeobj-message-3-face)
           '("^\\*\\* ok, .*$" . cafeobj-message-3-face)
           '("\\<\\(trying .*\\)\\>:" 0 cafeobj-message-2-face)
           '("^\\*\\* check .*:" . cafeobj-message-2-face)
           '("^\\*\\* Fail.*$" . cafeobj-message-3-face)
           '("^\\*\\* fail!$" . cafeobj-message-3-face)
           '("^\\*\\* Predicate .*$". cafeobj-message-3-face)
           '("^\\*\\* PigNose .*$" . cafeobj-message-2-face)
           '("^\\*\\* Search .*$" . cafeobj-process-keyword-face)
           ;; reduction
           '("^\\(-- reduce in .* :\\) " 1 cafeobj-message-1-face)
           '("^\\(-- behavioural reduce in .* :\\) " 1 cafeobj-message-1-face)
           '("^\\(-- cbred in .* :\\)" 1 cafeobj-message-1-face)
           '("^\\(#[0-9]+\\)(" 1 cafeobj-comment-face-1)
           ;; CITP
           '("^\\[.+\\].*$" . cafeobj-message-1-face)
           ;; '("\\<done.$" . cafeobj-message-2-face)
           '("^\\(case #.*:\\) " 1 cafeobj-message-1-face)
           '("^|  .*|$" . cafeobj-message-2-face)
           '("** __+$" . cafeobj-message-1-face)
           ;; '("^\\*\\*.*$" . cafeobj-comment-face-1)
           '("^\\*\\* USABLE " . cafeobj-process-keyword-face)
           '("^\\*\\* SOS " . cafeobj-process-keyword-face)
           '("^\\*\\* PASSIVE " . cafeobj-process-keyword-face)
           '("^\\*\\* Starting PigNose " . cafeobj-process-keyword-face)
           '("^\\*\\* DEMODULATORS " . cafeobj-process-keyword-face)
           '("^\\*\\* PROOF " . cafeobj-process-keyword-face)
           '("^___+$" . cafeobj-message-2-face)
           '("^---+$" . cafeobj-message-2-face)
           '("^adding axiom:" . cafeobj-comment-face-2)
           '("^goal:" . cafeobj-message-1-face)
           '("^hypo:" . cafeobj-comment-face-2)
           '("^ax:" . cafeobj-message-1-face)
           '("^==.*$" . cafeobj-message-2-face)
           '("[ \t]\\([+-][^ \t\n>]+\\)" 1 cafeobj-option-face)
           ;; '("^[^\n]+.*$" . cafeobj-output-face)
           )
     cafeobj-font-lock-keywords)))

(put 'cafeobj-process-mode 'font-lock-defaults
     '(cafeobj-process-font-lock-keywords t))

;;; CafeOBJ Process Mode

(defun cafeobj-process-mode ()
  (interactive)
  (comint-mode)
  (setq major-mode 'CafeOBJ-process-mode)
  (setq mode-name "CafeOBJ process")
  (use-local-map cafeobj-process-mode-map)
  (make-local-variable 'comint-prompt-regexp)
  (setq comint-prompt-regexp cafeobj-prompt-pattern)
  (setq comint-completion-fignore cafeobj-completion-fignore)
  (make-local-variable 'comint-delimiter-argument-list)
  (setq comint-delimiter-argument-list cafeobj-delimiter-argument-list)
  (setq comint-file-name-chars cafeobj-file-name-chars)
  (setq comint-file-name-quote-list cafeobj-file-name-quote-list)
  (set (make-local-variable 'comint-dynamic-complete-functions)
       cafeobj-dynamic-complete-functions)
  (make-local-variable 'paragraph-start)
  (setq paragraph-start comint-prompt-regexp)
  (make-local-variable 'font-lock-defaults)
  (setq font-lock-defaults '(cafeobj-process-font-lock-keywords t))
  (make-local-variable 'cafeobj-dirstack)
  (setq cafeobj-dirstack nil)
  (make-local-variable 'cafeobj-last-dir)
  (setq cafeobj-last-dir nil)
  (make-local-variable 'cafeobj-dirtrackp)
  (setq cafeobj-dirtrackp t)
  (add-hook 'comint-input-filter-functions 'cafeobj-directory-tracker nil t)
  (setq comint-input-autoexpand cafeobj-input-autoexpand)
  ;; This is not really correct, since the CafeOBJ buffer does not really
  ;; edit this directory.  But it is useful in the buffer list and menus.
  (make-local-variable 'list-buffers-directory)
  (setq list-buffers-directory (expand-file-name default-directory))
  (setq cafeobj-dirstack-query "pwd")
  (run-hooks 'cafeobj-process-mode-hook)
  (comint-read-input-ring t)
  (cafeobj-dirstack-message)
  )

(defun cafeobj-start-process (name program &optional startfile &rest switches)
  "Start a chaos process named NAME, running PROGRAM."
  (or switches
      (setq switches cafeobj-default-command-switches))
  (when cafeobj-xemacs-p
    (setq switches (append switches '("-no-banner"))))
  (setq cafeobj-process-buffer (apply 'make-comint name program startfile switches))
  (setq cafeobj-process (get-buffer-process cafeobj-process-buffer))
  (save-excursion
    (set-buffer cafeobj-process-buffer)
    (cafeobj-process-mode)))

(defcustom cafeobj-logo-file "/usr/local/share/doc/cafeobj/cafeobj-logo-small.png"
  "CafeOBJ's logo file displayed at start up time of the interpreter."
  :type 'string
  :group 'cafeobj)

(defun cafeobj-startup-message (&optional x y)
  "Insert startup message in current buffer."
  (erase-buffer)
  (when (and (display-graphic-p)
             (file-exists-p cafeobj-logo-file))
    (let* ((img (create-image cafeobj-logo-file))
           (img-size (image-size img))
           (char-per-pixel (/ (* 1.0 (window-width)) (window-pixel-width))))
      (goto-char (point-min))
      (insert " \n")
      (insert-image img)
      (while (not (eobp))
        (insert (make-string (truncate (* (/ (max (- (window-pixel-width)
                                                     (or x (car img-size)))
                                                  0)
                                             2)
                                          char-per-pixel))
                             ?\ ))
        (forward-line 1))))
  (goto-char (point-max))
  (insert (make-string 2 ?\n))
  (set-buffer-modified-p t))

(defun cafeobj (&rest ignore)
  (interactive)
  (if (and cafeobj-process
           (eq (process-status cafeobj-process) 'run))
      (switch-to-buffer cafeobj-process-buffer)
    (progn
      (switch-to-buffer (get-buffer-create (concat "*" cafeobj-application-name "*")))
      ;; show cafeobj logo
      (cafeobj-startup-message)
      ;; start the process
      (cafeobj-start-process cafeobj-application-name cafeobj-default-application))))

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
        (cafeobj-start-process cafeobj-application-name cafeobj-default-application))
    (comint-simple-send cafeobj-process (buffer-substring start end))
    (forward-line 1)
    (if cafeobj-always-show
        (display-buffer cafeobj-process-buffer))))

(defun cafeobj-send-region (start end)
  "Send region to chaos subprocess."
  (interactive "r")
  (when (and start end) 
    (or (and cafeobj-process
             (comint-check-proc cafeobj-process-buffer))
        (cafeobj-start-process cafeobj-application-name cafeobj-default-application))
    (comint-simple-send cafeobj-process
                        (concat (buffer-substring start end) "\n"))
    (if cafeobj-always-show
        (display-buffer cafeobj-process-buffer))))

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
        (cafeobj-start-process cafeobj-application-name cafeobj-default-application))
    (comint-simple-send cafeobj-process
                        (concat (buffer-substring beg end) "\n"))
    (if cafeobj-always-show
        (display-buffer cafeobj-process-buffer))))

(defun cafeobj-send-buffer ()
  "Send whole buffer to chaos subprocess."
  (interactive)
  (or (and cafeobj-process
           (comint-check-proc cafeobj-process-buffer))
      (cafeobj-start-process cafeobj-application-name cafeobj-default-application))
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

;;; Directory tracking
;;;
;;; This code provides the shell mode input sentinel
;;;     CAFEOBJ-DIRECTORY-TRACKER
;;; that tracks cd, pushd, and popd commands issued to the shell, and
;;; changes the current directory of the shell buffer accordingly.
;;;
;;; This is basically a fragile hack, although it's more accurate than
;;; the version in Emacs 18's shell.el. It has the following failings:
;;; 1. It doesn't know about the cdpath shell variable.
;;; 2. It cannot infallibly deal with command sequences, though it does well
;;;    with these and with ignoring commands forked in another shell with ()s.
;;; 3. More generally, any complex command is going to throw it. Otherwise,
;;;    you'd have to build an entire shell interpreter in emacs lisp.  Failing
;;;    that, there's no way to catch shell commands where cd's are buried
;;;    inside conditional expressions, aliases, and so forth.
;;;
;;; The whole approach is a crock. Shell aliases mess it up. File sourcing
;;; messes it up. You run other processes under the shell; these each have
;;; separate working directories, and some have commands for manipulating
;;; their w.d.'s (e.g., the lcd command in ftp). Some of these programs have
;;; commands that do *not* affect the current w.d. at all, but look like they
;;; do (e.g., the cd command in ftp).  In shells that allow you job
;;; control, you can switch between jobs, all having different w.d.'s. So
;;; simply saying %3 can shift your w.d..
;;;
;;; The solution is to relax, not stress out about it, and settle for
;;; a hack that works pretty well in typical circumstances. Remember
;;; that a half-assed solution is more in keeping with the spirit of Unix, 
;;; anyway. Blech.
;;;
;;; One good hack not implemented here for users of programmable shells
;;; is to program up the shell w.d. manipulation commands to output
;;; a coded command sequence to the tty. Something like
;;;     ESC | <cwd> |
;;; where <cwd> is the new current working directory. Then trash the
;;; directory tracking machinery currently used in this package, and
;;; replace it with a process filter that watches for and strips out
;;; these messages.

(defun cafeobj-directory-tracker (str)
  "Tracks cd, pushd and popd commands issued to the shell.
This function is called on each input passed to the shell.
It watches for cd, pushd and popd commands and sets the buffer's
default directory to track these commands.

You may toggle this tracking on and off with \\[dirtrack-toggle].
If emacs gets confused, you can resync with the shell with \\[dirs].

See variables `cafeobj-cd-regexp', `cafeobj-chdrive-regexp', `cafeobj-pushd-regexp',
and  `cafeobj-popd-regexp', while `cafeobj-pushd-tohome', `cafeobj-pushd-dextract', 
and `cafeobj-pushd-dunique' control the behavior of the relevant command.

Environment variables are expanded, see function `substitute-in-file-name'."
  (if cafeobj-dirtrackp
      ;; We fail gracefully if we think the command will fail in the shell.
      (condition-case chdir-failure
          (let ((start (progn (string-match "^[; \t]*" str) ; skip whitespace
                              (match-end 0)))
                end cmd arg1)
            (while (string-match cafeobj-command-regexp str start)
              (setq end (match-end 0)
                    cmd (comint-arguments (substring str start end) 0 0)
                    arg1 (comint-arguments (substring str start end) 1 1))
              (cond ((string-match (concat "\\`\\(" cafeobj-popd-regexp
                                           "\\)\\($\\|[ \t]\\)")
                                   cmd)
                     (cafeobj-process-popd (comint-substitute-in-file-name arg1)))
                    ((string-match (concat "\\`\\(" cafeobj-pushd-regexp
                                           "\\)\\($\\|[ \t]\\)")
                                   cmd)
                     (cafeobj-process-pushd (comint-substitute-in-file-name arg1)))
                    ((string-match (concat "\\`\\(" cafeobj-cd-regexp
                                           "\\)\\($\\|[ \t]\\)")
                                   cmd)
                     (cafeobj-process-cd (comint-substitute-in-file-name arg1)))
                    ((and cafeobj-chdrive-regexp
                          (string-match (concat "\\`\\(" cafeobj-chdrive-regexp
                                                "\\)\\($\\|[ \t]\\)")
                                        cmd))
                     (cafeobj-process-cd (comint-substitute-in-file-name cmd))))
              (setq start (progn (string-match "[; \t]*" str end) ; skip again
                                 (match-end 0)))))
    (error "Couldn't cd"))))


;; Like `cd', but prepends comint-file-name-prefix to absolute names.
(defun cafeobj-cd-1 (dir dirstack)
  (if cafeobj-dirtrackp
      (setq list-buffers-directory (file-name-as-directory
                                    (expand-file-name dir))))
  (condition-case nil
      (progn (if (file-name-absolute-p dir)
                 ;;(cd-absolute (concat comint-file-name-prefix dir))
                 (cd-absolute dir)
               (cd dir))
             (setq cafeobj-dirstack dirstack)
             (cafeobj-dirstack-message))
    (file-error (message "Couldn't cd."))))

;;; popd [+n]
(defun cafeobj-process-popd (arg)
  (let ((num (or (cafeobj-extract-num arg) 0)))
    (cond ((and num (= num 0) cafeobj-dirstack)
           (cafeobj-cd-1 (car cafeobj-dirstack) (cdr cafeobj-dirstack)))
          ((and num (> num 0) (<= num (length cafeobj-dirstack)))
           (let* ((ds (cons nil cafeobj-dirstack))
                  (cell (nthcdr (1- num) ds)))
             (rplacd cell (cdr (cdr cell)))
             (setq cafeobj-dirstack (cdr ds))
             (cafeobj-dirstack-message)))
          (t
           (error "Couldn't popd")))))

;; Return DIR prefixed with comint-file-name-prefix as appropriate.
(defun cafeobj-prefixed-directory-name (dir)
  (if (= (length comint-file-name-prefix) 0)
      dir
    (if (file-name-absolute-p dir)
        ;; The name is absolute, so prepend the prefix.
        (concat comint-file-name-prefix dir)
      ;; For relative name we assume default-directory already has the prefix.
      (expand-file-name dir))))

;;; cd [dir]
(defun cafeobj-process-cd (arg)
  (let ((new-dir (cond ((zerop (length arg)) (concat comint-file-name-prefix
                                                     "~"))
                       ((string-equal "-" arg) cafeobj-last-dir)
                       (t (cafeobj-prefixed-directory-name arg)))))
    (setq cafeobj-last-dir default-directory)
    (cafeobj-cd-1 new-dir cafeobj-dirstack)))

;;; pushd [+n | dir]
(defun cafeobj-process-pushd (arg)
  (let ((num (cafeobj-extract-num arg)))
    (cond ((zerop (length arg))
           ;; no arg -- swap pwd and car of stack unless cafeobj-pushd-tohome
           (cond (cafeobj-pushd-tohome
                  (cafeobj-process-pushd (concat comint-file-name-prefix "~")))
                 (cafeobj-dirstack
                  (let ((old default-directory))
                    (cafeobj-cd-1 (car cafeobj-dirstack)
                                (cons old (cdr cafeobj-dirstack)))))
                 (t
                  (message "Directory stack empty."))))
          ((numberp num)
           ;; pushd +n
           (cond ((> num (length cafeobj-dirstack))
                  (message "Directory stack not that deep."))
                 ((= num 0)
                  (error (message "Couldn't cd.")))
                 (cafeobj-pushd-dextract
                  (let ((dir (nth (1- num) cafeobj-dirstack)))
                    (cafeobj-process-popd arg)
                    (cafeobj-process-pushd default-directory)
                    (cafeobj-cd-1 dir cafeobj-dirstack)))
                 (t
                  (let* ((ds (cons default-directory cafeobj-dirstack))
                         (dslen (length ds))
                         (front (nthcdr num ds))
                         (back (reverse (nthcdr (- dslen num) (reverse ds))))
                         (new-ds (append front back)))
                    (cafeobj-cd-1 (car new-ds) (cdr new-ds))))))
          (t
           ;; pushd <dir>
           (let ((old-wd default-directory))
             (cafeobj-cd-1 (cafeobj-prefixed-directory-name arg)
                         (if (or (null cafeobj-pushd-dunique)
                                 (not (member old-wd cafeobj-dirstack)))
                             (cons old-wd cafeobj-dirstack)
                             cafeobj-dirstack)))))))

;; If STR is of the form +n, for n>0, return n. Otherwise, nil.
(defun cafeobj-extract-num (str)
  (and (string-match "^\\+[1-9][0-9]*$" str)
       (string-to-number str)))

(defun cafeobj-dirtrack-toggle ()
  "Turn directory tracking on and off in a shell buffer."
  (interactive)
  (if (setq cafeobj-dirtrackp (not cafeobj-dirtrackp))
      (setq list-buffers-directory default-directory)
    (setq list-buffers-directory nil))
  (message "Directory tracking %s" (if cafeobj-dirtrackp "ON" "OFF")))

;;; For your typing convenience:
(defalias 'dirtrack-toggle 'cafeobj-dirtrack-toggle)

(defun cafeobj-cd (dir)
  "Do normal `cd' to DIR, and set `list-buffers-directory'."
  (if cafeobj-dirtrackp
      (setq list-buffers-directory (file-name-as-directory
                                    (expand-file-name dir))))
  (cd dir))

(defun cafeobj-resync-dirs ()
  "Resync the buffer's idea of the current directory stack.
This command queries the shell with the command bound to 
`cafeobj-dirstack-query' (default \"dirs\"), reads the next
line output and parses it to form the new directory stack.
DON'T issue this command unless the buffer is at a shell prompt.
Also, note that if some other subprocess decides to do output
immediately after the query, its output will be taken as the
new directory stack -- you lose. If this happens, just do the
command again."
  (interactive)
  (let* ((proc (get-buffer-process (current-buffer)))
         (pmark (process-mark proc)))
    (goto-char pmark)
    (insert cafeobj-dirstack-query) (insert "\n")
    (sit-for 0) ; force redisplay
    (comint-send-string proc cafeobj-dirstack-query) 
    (comint-send-string proc "\n")
    (set-marker pmark (point))
    (let ((pt (point))) ; wait for 1 line
      ;; This extra newline prevents the user's pending input from spoofing us.
      (insert "\n") (backward-char 1)
      (while (not (looking-at ".+\n"))
        (accept-process-output proc)
        (goto-char pt)
        ;; kludge to cope with shells that have "stty echo" turned on.
        ;; of course this will lose if there is only one dir on the stack
        ;; and it is named "dirs"...  -jwz
        (if (looking-at "^dirs\r?\n") (delete-region (point) (match-end 0)))
        ))
    (goto-char pmark) (delete-char 1) ; remove the extra newline
    ;; That's the dirlist. grab it & parse it.
    (let* ((dl (buffer-substring (match-beginning 0) (1- (match-end 0))))
           (dl-len (length dl))
           (ds '())                     ; new dir stack
           (i 0))
      (while (< i dl-len)
        ;; regexp = optional whitespace, (non-whitespace), optional whitespace
        (string-match "\\s *\\(\\S +\\)\\s *" dl i) ; pick off next dir
        (setq ds (cons (concat comint-file-name-prefix
                               (substring dl (match-beginning 1)
                                          (match-end 1)))
                       ds))
        (setq i (match-end 0)))
      (let ((ds (reverse ds)))
        (cafeobj-cd-1 (car ds) (cdr ds))))))

;;; For your typing convenience:
(defalias 'dirs 'cafeobj-resync-dirs)

;; XEmacs addition
(defvar cafeobj-dirstack-message-hook nil
  "Hook to run after a cd, pushd or popd event")

;;; Show the current dirstack on the message line.
;;; Pretty up dirs a bit by changing "/usr/jqr/foo" to "~/foo".
;;; (This isn't necessary if the dirlisting is generated with a simple "dirs".)
;;; All the commands that mung the buffer's dirstack finish by calling
;;; this guy.
(defun user-home-directory ()
  (getenv "HOME"))

(defun cafeobj-dirstack-message ()
  (let* ((msg "")
         (ds (cons default-directory cafeobj-dirstack))
         (home (if cafeobj-xemacs-p
                   (format "^%s\\(/\\|$\\)"
                           (regexp-quote (user-home-directory)))
                 abbreviated-home-dir))
         (prefix (and comint-file-name-prefix
                      ;; XEmacs addition: don't turn "/foo" into "foo" !!
                      (not (= 0 (length comint-file-name-prefix)))
                      (format "^%s\\(/\\|$\\)"
                              (regexp-quote comint-file-name-prefix)))))
    (while ds
      (let ((dir (car ds)))
        (if (string-match home dir)
            (setq dir (concat "~/" (substring dir (match-end 0)))))
        ;; Strip off comint-file-name-prefix if present.
        (and prefix (string-match prefix dir)
             (setq dir (substring dir (match-end 0)))
             (setcar ds dir)
             )
        (setq msg (concat msg dir " "))
        (setq ds (cdr ds))))
    (run-hooks 'cafeobj-dirstack-message-hook)
    (message "%s" msg)))

;; This was mostly copied from cafeobj-resync-dirs.
(defun cafeobj-snarf-envar (var)
  "Return as a string the shell's value of environment variable VAR."
  (let* ((cmd (format "printenv '%s'\n" var))
         (proc (get-buffer-process (current-buffer)))
         (pmark (process-mark proc)))
    (goto-char pmark)
    (insert cmd)
    (sit-for 0)                         ; force redisplay
    (comint-send-string proc cmd)
    (set-marker pmark (point))
    (let ((pt (point)))                 ; wait for 1 line
      ;; This extra newline prevents the user's pending input from spoofing us.
      (insert "\n") (backward-char 1)
      (while (not (looking-at ".+\n"))
        (accept-process-output proc)
        (goto-char pt)))
    (goto-char pmark) (delete-char 1)   ; remove the extra newline
    (buffer-substring (match-beginning 0) (1- (match-end 0)))))

(defun cafeobj-copy-environment-variable (variable)
  "Copy the environment variable VARIABLE from the subshell to Emacs.
This command reads the value of the specified environment variable
in the shell, and sets the same environment variable in Emacs
\(what `getenv' in Emacs would return) to that value.
That value will affect any new subprocesses that you subsequently start
from Emacs."
  (interactive (list (read-envvar-name "\
Copy Shell environment variable to Emacs: ")))
  (setenv variable (cafeobj-snarf-envar variable)))

(defun cafeobj-forward-command (&optional arg)
  "Move forward across ARG shell command(s).  Does not cross lines.
See `cafeobj-command-regexp'."
  (interactive "p")
  (let ((limit (save-excursion (end-of-line nil) (point))))
    (if (re-search-forward (concat cafeobj-command-regexp "\\([;&|][\t ]*\\)+")
                           limit 'move arg)
        (skip-syntax-backward " "))))


(defun cafeobj-backward-command (&optional arg)
  "Move backward across ARG shell command(s).  Does not cross lines.
See `cafeobj-command-regexp'."
  (interactive "p")
  (let ((limit (save-excursion (comint-bol nil) (point))))
    (if (> limit (point))
        (save-excursion (beginning-of-line) (setq limit (point))))
    (skip-syntax-backward " " limit)
    (if (re-search-backward
         (format "[;&|]+[\t ]*\\(%s\\)" cafeobj-command-regexp) limit 'move arg)
        (progn (goto-char (match-beginning 1))
               (skip-chars-forward ";&|")))))

(defvar esc-esc "")

(defun cafeobj-put-esc-esc ()
  "send EscEsc to CafeOBJ process. This makes the interpeter
to cancel current input."
  (interactive)
  (let* ((proc (get-buffer-process (current-buffer)))
         (pmark (process-mark proc)))
    (goto-char pmark)
    (comint-send-string proc esc-esc)
    (comint-send-string proc "\n")
    (set-marker pmark (point))))

(defun cafeobj-dynamic-complete-command ()
  "Dynamically complete the command at point.
This function is similar to `comint-dynamic-complete-filename', except that it
searches `exec-path' (minus the trailing emacs library path) for completion
candidates.  Note that this may not be the same as the shell's idea of the
path.

Returns t if successful."
  (interactive)
  (let ((filename (comint-match-partial-filename)))
    (if (and filename
             (save-match-data (not (string-match "[~/]" filename)))
             (eq (match-beginning 0)
                 (save-excursion (cafeobj-backward-command 1) (point))))
        (prog2 (message "Completing command name...")
            (cafeobj-dynamic-complete-as-command)))))


(defun cafeobj-dynamic-complete-as-command ()
  "Dynamically complete at point as a command.
See `cafeobj-dynamic-complete-filename'.  Returns t if successful."
  (let* ((filename (or (comint-match-partial-filename) ""))
         (pathnondir (file-name-nondirectory filename))
         (paths (cdr (reverse exec-path)))
         (cwd (file-name-as-directory (expand-file-name default-directory)))
         (ignored-extensions
          (and comint-completion-fignore
               (mapconcat (function (lambda (x) (concat (regexp-quote x) "$")))
                          comint-completion-fignore "\\|")))
         (path "") (comps-in-path ()) (file "") (filepath "") (completions ()))
    ;; Go thru each path in the search path, finding completions.
    (while paths
      (setq path (file-name-as-directory (comint-directory (or (car paths) ".")))
            comps-in-path (and (file-accessible-directory-p path)
                               (file-name-all-completions pathnondir path)))
      ;; Go thru each completion found, to see whether it should be used.
      (while comps-in-path
        (setq file (car comps-in-path)
              filepath (concat path file))
        (if (and (not (member file completions))
                 (not (and ignored-extensions
                           (string-match ignored-extensions file)))
                 (or (string-equal path cwd)
                     (not (file-directory-p filepath)))
                 )
            (setq completions (cons file completions)))
        (setq comps-in-path (cdr comps-in-path)))
      (setq paths (cdr paths)))
    ;; OK, we've got a list of completions.
    (let ((success (let ((comint-completion-addsuffix nil))
                     (comint-dynamic-simple-complete pathnondir completions))))
      (if (and (memq success '(sole shortest)) comint-completion-addsuffix
               (not (file-directory-p (comint-match-partial-filename))))
          (insert " "))
      success)))

(defun cafeobj-dynamic-complete-filename ()
  "Dynamically complete the filename at point.
This completes only if point is at a suitable position for a
filename argument."
  (interactive)
  (let ((opoint (point))
        (beg (comint-line-beginning-position)))
    (when (save-excursion
            (goto-char (if (re-search-backward "[;|&]" beg t)
                           (match-end 0)
                         beg))
            (re-search-forward "[^ \t][ \t]" opoint t))
      (comint-dynamic-complete-as-filename))))

(defun cafeobj-match-partial-variable ()
  "Return the shell variable at point, or nil if none is found."
  (save-excursion
    (let ((limit (point)))
      (if (re-search-backward "[^A-Za-z0-9_{}]" nil 'move)
          (or (looking-at "\\$") (forward-char 1)))
      ;; Anchor the search forwards.
      (if (or (eolp) (looking-at "[^A-Za-z0-9_{}$]"))
          nil
        (re-search-forward "\\$?{?[A-Za-z0-9_]*}?" limit)
        (buffer-substring (match-beginning 0) (match-end 0))))))


(defun cafeobj-dynamic-complete-environment-variable ()
  "Dynamically complete the environment variable at point.
Completes if after a variable, i.e., if it starts with a \"$\".
See `cafeobj-dynamic-complete-as-environment-variable'.

This function is similar to `comint-dynamic-complete-filename', except that it
searches `process-environment' for completion candidates.  Note that this may
not be the same as the interpreter's idea of variable names.  The main problem
with this type of completion is that `process-environment' is the environment
which Emacs started with.  Emacs does not track changes to the environment made
by the interpreter.  Perhaps it would be more accurate if this function was
called `cafeobj-dynamic-complete-process-environment-variable'.

Returns non-nil if successful."
  (interactive)
  (let ((variable (cafeobj-match-partial-variable)))
    (if (and variable (string-match "^\\$" variable))
        (prog2 (message "Completing variable name...")
            (cafeobj-dynamic-complete-as-environment-variable)))))


(defun cafeobj-dynamic-complete-as-environment-variable ()
  "Dynamically complete at point as an environment variable.
Used by `cafeobj-dynamic-complete-environment-variable'.
Uses `comint-dynamic-simple-complete'."
  (let* ((var (or (cafeobj-match-partial-variable) ""))
         (variable (substring var (or (string-match "[^$({]\\|$" var) 0)))
         (variables (mapcar (function (lambda (x)
                                        (substring x 0 (string-match "=" x))))
                            process-environment))
         (addsuffix comint-completion-addsuffix)
         (comint-completion-addsuffix nil)
         (success (comint-dynamic-simple-complete variable variables)))
    (if (memq success '(sole shortest))
        (let* ((var (cafeobj-match-partial-variable))
               (variable (substring var (string-match "[^$({]" var)))
               (protection (cond ((string-match "{" var) "}")
                                 ((string-match "(" var) ")")
                                 (t "")))
               (suffix (cond ((null addsuffix) "")
                             ((file-directory-p
                               (comint-directory (getenv variable))) "/")
                             (t " "))))
          (insert protection suffix)))
    success))


(defun cafeobj-replace-by-expanded-directory ()
  "Expand directory stack reference before point.
Directory stack references are of the form \"=digit\" or \"=-\".
See `default-directory' and `cafeobj-dirstack'.

Returns t if successful."
  (interactive)
  (if (comint-match-partial-filename)
      (save-excursion
        (goto-char (match-beginning 0))
        (let ((stack (cons default-directory cafeobj-dirstack))
              (index (cond ((looking-at "=-/?")
                            (length cafeobj-dirstack))
                           ((looking-at "=\\([0-9]+\\)")
                            (string-to-number
                             (buffer-substring
                              (match-beginning 1) (match-end 1)))))))
          (cond ((null index)
                 nil)
                ((>= index (length stack))
                 (error "Directory stack not that deep."))
                (t
                 (replace-match (file-name-as-directory (nth index stack)) t t)
                 (message "Directory item: %d" index)
                 t))))))



;;;
(defvar menu-bar-mode (featurep 'menubar))

(defgroup cafeobj-xmas nil
  "XEmacs support for CafeOBJ"
  :group 'cafeobj)

(defcustom cafeobj-glyph-directory "/usr/local/cafeobj-1.4/icons"
  "Directory where CafeOBJ logos and icons are located."
  :type '(choice (const :tag "autodetect" nil)
          directory)
  :group 'cafeobj)

(defvar cafeobj-xmas-logo-color-alist
  '((flame "#cc3300" "#ff2200")
    (pine "#c0cc93" "#f8ffb8")
    (moss "#a1cc93" "#d2ffb8")
    (irish "#04cc90" "#05ff97")
    (sky "#049acc" "#05deff")
    (tin "#6886cc" "#82b6ff")
    (velvet "#7c68cc" "#8c82ff")
    (grape "#b264cc" "#cf7df")
    (labia "#cc64c2" "#fd7dff")
    (berry "#cc6485" "#ff7db5")
    (neutral "#b4b4b4" "#878787")
    (september "#bf9900" "#ffcc00"))
  "Color alist used for the Gnus logo.")

(defcustom cafeobj-xmas-logo-color-style 'moss
  "*Color styles used for the CafeOBJ logo."
  :type '(choice (const flame) (const pine) (const moss)
                 (const irish) (const sky) (const tin)
                 (const velvet) (const grape) (const labia)
                 (const berry) (const neutral) (const september))
  :group 'cafeobj-xmas)

(defvar cafeobj-xmas-logo-colors
  (cdr (assq cafeobj-xmas-logo-color-style cafeobj-xmas-logo-color-alist))
  "Colors used for the CafeOBJ logo.")

(defvar cafeobj-xpm-size '(142 . 165))

;; (defun cafeobj-startup-message (&optional x y)
;;   "insert startup message in current buffer."
;;   ;; Insert the message.
;;   (setq cafeobj-glyph-directory
;;     "/usr/local/cafeobj-1.4/icons")
;;   (erase-buffer)
;;   (cond
;;    ((and (console-on-window-system-p)
;;       (or (featurep 'xpm)
;;           (featurep 'xbm)))
;;     (let* ((logo-xpm (expand-file-name "cafe-logo.xpm" cafeobj-glyph-directory))
;;         (logo-xbm (expand-file-name "cafe-logo.xbm" cafeobj-glyph-directory))
;;         (glyph (make-glyph
;;                 (cond ((featurep 'xpm)
;;                        `[xpm
;;                          :file ,logo-xpm
;;                          :color-symbols
;;                          (("thing" . ,(car cafeobj-xmas-logo-colors))
;;                           ("shadow" . ,(cadr cafeobj-xmas-logo-colors))
;;                           ("background" . ,(face-background 'default)))])
;;                       ((featurep 'xbm)
;;                        `[xbm :file ,logo-xbm])
;;                       (t [nothing]))))
;;         (char-per-pixel
;;          (/ (* 1.0 (window-width)) (window-pixel-width)))
;;         )
;;       (insert " ")
;;       (set-extent-begin-glyph (make-extent (point) (point)) glyph)
;;       (goto-char (point-min))
;;       (while (not (eobp))
;;      (insert (make-string (truncate
;;                            (* (/ (max (- (window-pixel-width)
;;                                          (or x
;;                                              (car cafeobj-xpm-size)))
;;                                       0)
;;                                  2)
;;                               char-per-pixel))
;;                           ?\ ))
;;      (forward-line 1))
;;       )))
;;   ;;
;;   (goto-char (point-max))
;;   (insert (make-string 2 ?\n))
;;   ;;
;;   (set-buffer-modified-p t))

;;;
;;;
(defvar cafeobj-comment-face-1 'cafeobj-comment-face-1)
(defvar cafeobj-comment-face-2 'cafeobj-comment-face-2)
(defvar cafeobj-string-face 'cafeobj-string-face)
(defvar cafeobj-string-face-2 'cafeobj-string-face-2)
(defvar cafeobj-keyword-face 'cafeobj-keyword-face)
(defvar cafeobj-decl-keyword-face 'cafeobj-decl-keyword-face)
(defvar cafeobj-command-name-face 'cafeobj-command-name-face)
(defvar cafeobj-message-1-face 'cafeobj-message-1-face)
(defvar cafeobj-message-2-face 'cafeobj-message-2-face)
(defvar cafeobj-message-3-face 'cafeobj-message-3-face)
(defvar cafeobj-error-face 'cafeobj-error-face)
(defvar cafeobj-warning-face 'cafeobj-warning-face)
(defvar cafeobj-pignose-keyword-face 'cafeobj-pignose-keyword-face)
(defvar cafeobj-prompt-face 'cafeobj-prompt-face)
(defvar cafeobj-process-keyword-face 'cafeobj-process-keyword-face)
(defvar cafeobj-option-face 'cafeobj-option-face)
(defvar cafeobj-output-face 'cafeobj-output-face)



(provide 'cafeobj-mode)

;; Local Variables:
;; folded-file: t
;; End:

;;; cafeobj-mode.el ends here
