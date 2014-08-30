;; head.lisp
;;

;d; Module head
;d; ===========
;d;
;d; The module defined in head and related files will be used
;d; to implement the documentation mechanism for foo bar baz
;d;
;d; Toplevel functions
;d; ------------------
;d;
;d; repl-loop
;d;   the repl-loop implements the basic interaction with the
;d    user by providing a prompt and ...

(defun (repl-loop) ...)

;d;
;d; debug-handler
;d;   the debug-handler comes into action when a unparseable input
;d;   has been found

(defun (debug-handler ...) ...)

;d;
;d; Support functions
;d; -----------------
;d; .. include:: functions.rst
;d;


