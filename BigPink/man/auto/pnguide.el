(TeX-add-style-hook "pnguide"
 (function
  (lambda ()
    (LaTeX-add-bibitems
     "chang-lee"
     "ha"
     "otter"
     "cafeobj"
     "CafeRep")
    (TeX-run-style-hooks
     "minitoc"
     "fancyvrb"
     "proof"
     "graphicx"
     "latex2e"
     "jart10"
     "jarticle"
     "a4paper"
     "part1"
     "part2"
     "part3"
     "part4"
     "part5"
     "appendix"))))

