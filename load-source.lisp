(in-package :user)

(defparameter *top-files*
  '("." "chaos-package" "version"))
(defparameter *comlib*
  '("comlib" "globals" "macros" "print-utils" "message"
    "error" "misc" "string" "list" "dag" "fsys" "tree-display"
    "lex" "reader"))
(defparameter *primitives*
  '("chaos/primitives"
    "term" "defterm" "bobject2" "absntax" "script" "op-theory" "bmodexp"
    "bmodule2" "bview2" "parse-modexp" "normodexp"
    "bsort" "boperator" "baxioms" "gen-eval" "gen-print"
    "context" "term-utils" "substitution" "find" "print-object"))
(defparameter *term-parser*
  '("chaos/term-parser"
    "parse-engine" "parse-top"))
(defparameter *e-match*
  '("chaos/e-match"
    "match-utils" "match-system" "match-e" "match-idem"
    "match-z" "match-a" "match-c" "match-az" "match-cz"
    "match-ac" "match-acz" "match" "match2"))
(defparameter *construct*
  '("chaos/construct"
    "sort" "operator" "variable" "match-method" "axiom" "gen-rule"
    "cr" "rwl" "beh" "module" "trs"))
(defparameter *decafe*
  '("chaos/decafe"
    "mutils" "modmorph" "mrmap" "meval" "view" "mimport"))
(defparameter *cafein*
  '("chaos/cafein"
    "rengine"))
(defparameter *tools*
  '("chaos/tools"
    "regcheck" "regularize" "describe" "sort-tree" "module-tree"
    "show" "set" "op-check" "compat"))
(defparameter *eval*
  '("chaos/eval"
    "eval-mod" "eval-ast" "eval-ast2" "chaos-top"))
(defparameter *boot*
  '("chaos/boot"
    "preproc" "prelude" "builtins"))
(defparameter *tram*
  '("chaos/tram" "tram"))
(defparameter *psup*
  '("chaos/psup" "psup"))
(defparameter *thstuff*
  '("thstuff"
    "parse-apply" "basics" "eval-match" "eval-apply" "cexec"))
(defparameter *cafeobj*
  '("cafeobj"
    "cafeobjvar" "creader" "trans-com" "trans-decl" "command-proc"
    "command-top" "cafeobj-top"))

(defun load-cafeobj ()
  (dolist (module (list *top-files* *comlib* *primitives* *term-parser*
			*e-match* *construct* *decafe* *cafein* *tools*
			*eval* *boot* *tram* *psup* *thstuff* *cafeobj*))
    (let ((dir (car module))
	  (files (cdr module))
	  (path nil))
      (dolist (file files)
	;; (setq path (make-pathname :directory dir :name file :type "lisp"))
	(setq path (concatenate 'string dir "/" file ".lisp"))
	(load path)))))

;;; EOF
