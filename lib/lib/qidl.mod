** -*- Mode:CafeOBJ -*-
** $Id: qidl.mod,v 1.2 2007-01-24 10:03:39 sawada Exp $
** system: Chaos
** module: library
** file: qidl.mod
** -------------------------------------------------------------

** we want to be very explicit here
lispq
(progn 
  (setq *include-bool-save* *include-bool*)
  (setq *include-bool* nil))

sys:mod! QIDL
      principal-sort Id
{
  imports {
    protecting (QID)
    protecting (BOOL)
  }
  signature {
    pred _ < _ : Id Id  { prec: 51 }
  }
  axioms {
    var X : Id
    var Y : Id
    eq X < Y = #! (string< x y) .
  }
}

**
lispq
(setq *include-bool* *include-bool-save*)
**
provide QIDL
provide quidl
**
eof
