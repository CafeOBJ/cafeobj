;;; $Id: PosFLOAT.lisp,v 1.1.1.1 2003-06-19 08:30:17 sawada Exp $
;;; file: ~goguen/osa/PosFLOAT.lsp
;;; was: ~hanyan/PosFLOAT.lsp

;;; obj_PosFLOAT
(defun obj_PosFLOAT$is_PosFloat_token (token)
  (and
    (stringp token)
        (and (member (char token 0) '(#\+ #\.))
             (<= 2 (length token))
             (digit-char-p (char token 1)))
    (multiple-value-bind (res len) (read-from-string token)
        (declare (ignore res))
        (and (= (length token) len)
             (member (type-of (read-from-string token)) '(
                 #+LUCID float long-float short-float fixnum bignum ratio
                 #+CMU single-float #+CMU double-float
             ))))))
(defun obj_PosFLOAT$create_PosFloat (token)
  (coerce (read-from-string token) 'long-float))
(defun obj_PosFLOAT$print_PosFloat (val) (prin1 val))
(defun obj_PosFLOAT$is_PosFloat (val) (and (eq 'long-float (type-of val))
                                           (< 0 val)))

;;; obj_ANGLE
(defun obj_ANGLE$is_Angle_token (token)
  (and
    (stringp token)
        (and (member (char token 0) '(#\+ #\.))
             (<= 2 (length token))
             (digit-char-p (char token 1)))
    (multiple-value-bind (res len) (read-from-string token)
        (declare (ignore res))
        (and (= (length token) len)
             (member (type-of (read-from-string token)) '(
                 #+LUCID float long-float short-float fixnum bignum ratio
                 #+CMU single-float #+CMU double-float
             ))))))
(defun obj_ANGLE$create_Angle (token)
  (coerce (read-from-string token) 'long-float))
(defun obj_ANGLE$print_Angle (val) (prin1 val))
(defun obj_ANGLE$is_Angle (val)
  (and (eq 'long-float (type-of val))
       (< 0 val)
       (<= val (* 2 pi) )))
