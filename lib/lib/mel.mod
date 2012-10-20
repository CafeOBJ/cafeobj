**
** MEL sort constraint support
**
evq
(defun sort-match (x s &optional (module (or *current-module*
                                             *last-module*)))
  (unless module (return-from sort-match nil))
  (let ((so (module-sort-order module))
        (sort (find-sort-in module (string (term-builtin-value s)))))
    (unless sort (return-from sort-match nil))
    (sort<= (term-sort x) sort so)))

module! MEL
{
  protecting (CHAOS:IDENTIFIER)
  [ Identifier < SortName ]
  pred (_::_) : *Universal* SortName
  eq (X:*Universal* :: S:SortName) = #!!(coerce-to-Bool
					 (sort-match X S)) .
}

