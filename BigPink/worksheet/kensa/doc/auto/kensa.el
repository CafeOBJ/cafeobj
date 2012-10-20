(TeX-add-style-hook "kensa"
 (function
  (lambda ()
    (LaTeX-add-bibitems
     "otter")
    (TeX-run-style-hooks
     "ipa2000-layout"
     "latex2e"
     "jart11"
     "jarticle"
     "a4paper"
     "11pt"
     "part1"
     "part2"
     "part3"
     "part4"))))

