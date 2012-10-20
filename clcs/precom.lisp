;;; -*- Mode: Lisp; Syntax: Common-Lisp; Package: "CONDITIONS"; Base: 10 -*-

(in-package "CONDITIONS" :USE '("LISP" #+(and clos (not pcl)) "CLOS" #+pcl "PCL"))

#+pcl
(pcl::precompile-random-code-segments clcs)
