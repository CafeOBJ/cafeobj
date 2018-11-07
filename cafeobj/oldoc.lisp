;;;-*- Mode:LISP; Package:CHAOS; Base:10; Syntax:Common-lisp -*-
#|==============================================================================
                            System: CHAOS
                           Module: cafeobj
                          File: oldoc.lisp
==============================================================================|#
;;;
;;; Copyright (c) 2000-2015, Toshimi Sawada. All rights reserved.
;;; Copyright (c) 2014-2015, Norbert Preining. All rights reserved.
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
(in-package :chaos)
#-:chaos-debug
(declaim (optimize (speed 3) (safety 0) #-GCL (debug 0)))
#+:chaos-debug
(declaim (optimize (speed 1) (safety 3) #-GCL (debug 3)))


;;; *****************************************************
;;; On line document for commands, declarations or others 
;;; *****************************************************

;; In the online documentation system we have to deal with a variety
;; of string with lots of different relations to functionality.
;; 
;; Contents of oldoc entry
;; -----------------------
;; * title - shown on top of online output and as section head in print
;; * doc   - body of the documentation
;; * mdkey - the key used in the markdown version as anchor (\label)
;; * example - if present will be shown in the markdown version (print)
;;             and shown by ?ex
;; * related - a list of related concepts
;; * names - list of strings that where passed in during generation time
;; and one more, that is the
;; * key - a key into a hash table
;; 
;; 
;; How these strings are generated
;; -------------------------------
;; Generation of oldoc entries happen during (define "cmd" ...) calls in
;;   cafeobj/commands.lisp
;; and is governed by the following rules
;; * if no :doc key is present, no oldoc entry is generated
;; * if no :title key is present, then the first argument to (define ...) call
;;   is enclosed in backquotes and used as title.
;;   Example: (define ("full reset" "full-reset" "full") ...)
;;   does not have a :title key, so the string
;;     `full reset`
;;   is used as title.
;; * if no :mdkey is given, then the first argument is used as is.
;; 
;; Notes:
;; * key is generated by from the first entry in the define call
;;   via
;;      (oldoc-make-key <argument>)
;;   but then we have to sort via the reduced title, and there we have
;;   entries like "[sys:]module" entries which would be sorted wrongly
;; 
;; How search strings are used/parsed
;; ----------------------------------
;; "Search strings" are arguments passed to functions: ?, ?ex, ?ap
;; These functions are defined as :arg parsing, so we receive
;; (after some mangling) a list of strings as "question"
;; 
;; Example:
;;      ? clean   me
;; will call the various ? related functions with 
;;      question = ("clean" "me")
;; 
;; Notes: - argument parsing is space-disregarding, tokenizing after whitespace
;; - " quoted strings are only partially supported, if at all (WIP)
;; 
;; 
;; What and how search functions do
;; --------------------------------
;; * ? and ?ex behave in the same way:
;;   - strings searched
;;     . reduced title - strip all backquotes but leave otherwise as is
;;     . all names
;;     (do not search title as is, too much duplication!)
;;     procedure see below
;;   - how search is performed
;;     . format question argument list into one string with one space 
;;       separation
;;          ("clean" "`me`")  ->   "clean `me`"
;;     . create reduce version of it -> "clean me" (call this "redss")
;;     . generate key from redss
;;     . if this key gives a direct hit, use it
;;     . if not
;;       . for each entry in the main table
;;         . if redss prefix-match reduced title -> flag entry
;;         . for each alternative names (these are the arguments to define!)
;;           . if redss prefix-matches alternative name -> flag entry
;;       . if more than one entry is flagged, offer choices
;;       . if only one entry is flagged, display it
;;       
;; 
;; * ?ap
;;   - strings searched
;;     . full title, reduced title
;;     . all names
;;     . doc
;;     . ex
;;     format it as follow ~a~%~a~%~{~a~^~%~}~a~%~a
;;         full title, red title, ("all" "name") doc ex 
;;     Call the resulting string full search string "fullss"
;;     procedure see below
;;   - how search is performed
;;     . for each entry in the main table do
;;       . for each element x in the question list do
;;         . if x looks like a regex, do regex matching
;;         . otherwise do substring matching
;;       . if all the matches in the previous loop returned true, flag it
;;     . list all the flagged functions, or say no match

;;
;; INTERNAL functioons
;; not used outside this module
;;

(defvar *cafeobj-doc-db* (make-hash-table :test #'equal))
(defvar *cafeobj-alias-db* (make-hash-table :test #'equal))

(defstruct (oldoc (:print-function print-online-document))
  (key        ""  :type string)         ; 
  (category nil :type symbol)           ; cateogry name of the subject
  (main       ""  :type string)         ; document string of commad/declaration
  (title      ""  :type string)         ; title 
  (rtitle     ""  :type string)         ; reduced title for search
  (example    ""  :type string)         ; examples
  (mdkey      ""  :type string)         ; key written to reference manual
  (names      nil :type list)           ;
  (related    nil :type list)           ; related commands
  (cache nil)                           ; formatted doc cache for online help
  )

(defun print-online-document (doc &optional (stream *standard-output*) &rest ignore)
  (declare (ignore ignore))
  (format stream "~%*** key    : ~a" (oldoc-key doc))
  (format stream "~&red-title  : ~a" (oldoc-rtitle doc))
  (format stream "~&title      : ~a" (oldoc-title doc))
  (format stream "~&mdkey      : ~a" (oldoc-mdkey doc))
  (format stream "~&main       : ~a" (oldoc-main doc))
  (format stream "~&example    : ~a" (oldoc-example doc))
  (format stream "~&names      : ~a" (oldoc-names doc))
  (format stream "~&related    : ~a" (oldoc-related doc))
  (format stream "~&cache      : ~a" (oldoc-cache doc))
  (format stream "~&cateogry   : ~a" (oldoc-category doc)))

(defun oldoc-make-key (whatever)
  whatever)
;  (sxhash whatever))
(defun oldoc-question-to-string (question)
  (format nil "~{~a~^ ~}" question))


(defun oldoc-find-doc-entry (question)
  (let* ((redss (oldoc-reduce-string (oldoc-question-to-string question)))
         (key (oldoc-make-key redss))
         (docref (gethash key *cafeobj-alias-db*)))
    (if docref
        (gethash docref *cafeobj-doc-db*)
      ;; search for similar names
      (let* ((similar-keys nil) (redsslen (length redss)))
        (maphash #'(lambda (k v)
                     (if (and (>= (length (oldoc-rtitle v)) redsslen)
                              (string-equal redss (subseq (oldoc-rtitle v) 0 redsslen)))
                         (push (cons k (list (oldoc-title v))) similar-keys)
                       (dolist (n (oldoc-names v))
                         (if (and (>= (length n) redsslen)
                                  (string-equal redss (subseq n 0 redsslen)))
                             (progn
                               (push (cons k (list (oldoc-title v))) similar-keys)
                               (return))))))
                 *cafeobj-doc-db*)
        ;; if only one similar name is found, return the entry for it
        (if (= 1 (length similar-keys))
            (gethash (car (car similar-keys)) *cafeobj-doc-db*)
          ;; otherwise generate the list of " quoted possible names
          (map 'list #'(lambda (x) (concatenate 'string "\"" x "\""))
               (apply #'append (map 'list 'cdr similar-keys))))))))

(defun oldoc-format-related (doc &key (raw nil))
  (let (outlist targetdoc targettitle)
    (dolist (r (oldoc-related doc))
      (if (atom r)
          (progn
            (setq targettitle (format nil "`~a`" r))
            (setq targetdoc (oldoc-find-doc-entry (list r))))
        (progn
          (setq targettitle (car r))
          (if (cdr r)
              (setq targetdoc (oldoc-find-doc-entry (cdr r)))
            (setq targetdoc (oldoc-find-doc-entry (list (car r)))))))
      (if (listp targetdoc)
                                        ; problem - found several entries
          (if targetdoc
              (if raw
                  (push (format nil "\[~a\]\(\#~a\)" targettitle "multiple_targets") outlist)
                (push (format nil "~a" targettitle) outlist))
            (if raw
                (push (format nil "\[~a\]\(\#~a\)" targettitle "target_not_found") outlist)
              (push (format nil "~a" targettitle) outlist)))
        (if raw
            (push (format nil "\[~a\]\(\#~a\)" targettitle (oldoc-mdkey targetdoc)) outlist)
          (push (format nil "~a" targettitle) outlist))))
    (if outlist
        (format nil "~{~a~^, ~}" outlist)
        "")))

(defun oldoc-format-documentation (doc  &key (raw nil) (main t) (example nil) (related t))
  (let ((outstr "")
        (title (oldoc-title doc))
        (mainstr (oldoc-main doc))
        (exstr (oldoc-example doc))
        (relstr (oldoc-format-related doc :raw raw))
        (usecache (and main related (not raw) (not example))))
    (if (not raw)
        (or (and usecache (oldoc-cache doc))
            (progn
              (if main
                  (setq outstr (format nil "~a~2%~a~2%" title mainstr)))
                                        ; related dealing
              (if (and related (not (string-equal relstr "")))
                  (setq outstr (format nil "~aRelated: ~a~2%" outstr relstr)))
                                        ; example dealing
              (if (not (string-equal exstr ""))
                                        ; we have examples available
                  (if main
                      (if (not example)
                          (setq outstr (format nil "~a(Examples available)~2%" outstr))
                        (setq outstr (format nil "~aExamples:~%~a" outstr exstr)))
                      (if (not example)
                                        ; huu? don't show main and don't show examples?
                          (setq outstr (format nil "~a(Nothing to show?)~%" outstr))
                                        ; don't show main, but examples, add also title!
                        (setq outstr (format nil "Example(s) for ~a~2%~a" title exstr)))))
                                        ; manage cache
              (if usecache
                  (setf (oldoc-cache doc) (format-markdown outstr))
                (format-markdown outstr))))
        (progn
          ;; case for raw output
          (setq outstr (format nil "## ~a ## {#~a}~2%" title (oldoc-mdkey doc)))
          (if main
              (setq outstr (format nil "~a~a~2%" outstr mainstr)))
          (if (and related (not (string-equal relstr "")))
              (setq outstr (format nil "~aRelated: ~a~2%" outstr relstr)))
          (if (and example (not (string-equal exstr "")))
              (setq outstr (format nil "~a### Example ###~2%~a~2%" outstr exstr)))
          outstr))))


; (defun show-doc-entries ()
;   (let ((keys nil))
;     (maphash #'(lambda (k v) (declare (ignore v)) (push k keys)) *cafeobj-doc-db*)
;     (setq keys (sort keys #'string<=))
;     (dolist (key keys)
;       (let ((oldoc (get-document-string-from-doc (gethash key *cafeobj-doc-db*))))
;       (format t "~s" oldoc)))))

;;;
;;; search for an arbitrary regexp in all main strs, and return
;;; string that lists all possible matches
;;;
(defun oldoc-is-regex (re)
  (not (cl-ppcre:scan "^[\\w\\s]*$" re)))
(defun oldoc-parse-to-words (str)
  (let ((outlst nil) (re (cl-ppcre:create-scanner "
                    (?: 
                        (\")  
                        ((?>[^\\\"]*(?:\\.[^\\\"]*)*))\" 
                    |  
                        (')                           
                        ((?>[^\\']*(?:\\.[^\\']*)*))' 
                    |   
                        (
                            (?:\\.|[^\\\"'])*?           
                        )               
                        (                          
                            \\z | (?=([\\s]+)) | (?!^)(?=[\"']) 
                        )  
                    )"
                                     :extended-mode t)))
    (map 'list #'(lambda (x) (if (not (string-equal x "")) (push (string-trim "\"'" x) outlst))) 
         (cl-ppcre:all-matches-as-strings re str))
    outlst))

(defun oldoc-search-all (question)
  ; oldoc is special as ?ap is using the :comment reader, which means we
  ; get one string till the end of line as argument.
  (let ((retstr "") (matching-docs nil)
        (matchers (map 'list #'(lambda (x)
                                 (if (oldoc-is-regex x)
                                     (handler-case
                                         ; we might get a string that is not a proper regexp, 
                                         ; in this case fall back to use it as substring search
                                         (let ((re (cl-ppcre:create-scanner x :case-insensitive-mode :multi-line-mode)))
                                           (lambda (y) (cl-ppcre:scan re y)))
                                       (cl-ppcre:ppcre-syntax-error (condition)
                                         (format t "[Error] Cannot parse as regexp: ~S~%Treating it as normal string!~%"
                                                 (cl-ppcre:ppcre-syntax-error-string condition))
                                         (lambda (y) (search x y))))
                                   (lambda (y) (search x y))))
                       (oldoc-parse-to-words (car question)))))
    (maphash #'(lambda (key oldoc)
                 (declare (ignore key))
                 (let* ((fullss (oldoc-reduce-string (format nil "~a~%~{~a~^~%~}~a~%~a"
                                                             (oldoc-title oldoc)
                                                             (oldoc-names oldoc)
                                                             (oldoc-main oldoc)
                                                             (oldoc-example oldoc))))
                        (found (every #'identity
                                      (map 'list #'(lambda (x) 
                                                     (apply x (list fullss))) matchers))))
                   (when found
                     (push (oldoc-title oldoc) matching-docs))))
             *cafeobj-doc-db*)
                                        ; create the return string from the list of found keys
    (when matching-docs
      (setq retstr (format nil "Found the following matches:~% . ~{~a~^~% . ~}" matching-docs)))
    (if (string= retstr "")
        (setq retstr (format nil "No matches found!~%")))
    retstr))

;;;
;;;
;;; register-online-help : names doc 
;;;

  
(defun register-online-help (mainname aliasnames title mdkey doc example related &optional (category 'misc))
  (unless doc (return-from register-online-help nil))
  (unless (stringp doc) (return-from register-online-help nil))
  ; for each key generated from any name we generate an entry
  ; from that key to each key generated from the mainname
  ; (although there should be only one mainname and mainkey (?)
  (let ((mainkey (oldoc-make-key mainname)))
    (dolist (name (cons mainname aliasnames))
      (let ((key (oldoc-make-key name)))
        (setf (gethash key *cafeobj-alias-db*) mainkey)))
    ; if the tile is not given, we use the mainname enclosed in ` `
    ; if the mdkey is not given, we use the mainname as is
    (let* ((dt (or title (concatenate 'string "`" mainname "`")))
           (rt (oldoc-reduce-string dt)))
      (setf (gethash mainkey *cafeobj-doc-db*) 
            (make-oldoc :key mainkey
                        :main doc
                        :title dt
                        :rtitle rt
                        :mdkey (or mdkey (funcall #~s/^:/citp-/ mainname))
                        :example (or example "")
                        :related related
                        :names (cons mainname aliasnames)
                        :category category)))))

;;
;; format-markdown and oldoc-reduce-string are similar, but serve different
;; purpose:
;; * format-markdown is used when formattting a markdown string for
;;   online display
;; * oldoc-reduce-string is used as search basis of strings

(defparameter .md-remove-hash-hash. #~s/##//)
(defparameter .md-remove-link. #~s/{#.*}//)
(defparameter .md-remove-link2. #~s/\(#.+\)//)
(defparameter .md-remove-code-sign. #~s/~~//)
(defparameter .md-replace-tilde. #~s/~/*/)
(defparameter .md-replace-bq. #~s/`/'/)
(defparameter .md-remove-bq. #~s/`//)


(defun format-markdown (str)
  (funcall .md-replace-bq.
           (funcall .md-replace-tilde.
                    (funcall .md-remove-code-sign.
                             (funcall .md-remove-link2.
                                      (funcall .md-remove-link.
                                               (funcall .md-remove-hash-hash. str)))))))

(defun oldoc-reduce-string (str)
  (funcall .md-remove-bq.
           (funcall .md-remove-link2.
                    (funcall .md-remove-link.
                             (funcall .md-remove-hash-hash. str)))))



;;;
;;; Export
;;; export document string to a file.
;;;
(defvar .out-done. (make-hash-table :test #'equal))

; refman-sort determines the order in the reference manual based on the
; keys. For now we simply sort alphabetically but ignore leading :
; from the CITP commands, so that 
;   :foobar
; is sorted near f and not at the beginning.
(defun refman-sort (a b)
  (let ((aa (funcall #~s/^:// a)) (bb (funcall #~s/^:// b)))
     (string-lessp aa bb)))
  
(defun export-refman (&optional (output "manual/md/reference.md"))
  (clrhash .out-done.)
  (let (data)
    (with-open-file (out output :direction :output :if-exists :supersede :if-does-not-exist :create)
      (maphash #'(lambda (k oldoc) 
                   (let ((docstr (oldoc-format-documentation oldoc :raw t :main t :example t)))
                     (unless docstr
                       (error "The document string not found for ~s." k))
                     ; we would like to use the reduced title as sort criteria
                     ; but in this case we get problems with entries like
                     ; [sys:]module which is sorted around [ which is bad.
                     ; TODO: add a key sort string or recognize []?
                     ; (push (cons (oldoc-rtitle oldoc) docstr) data)))
                     (push (cons k docstr) data)))
               *cafeobj-doc-db*)
      (setq data (sort data #'refman-sort :key #'car))
      (dolist (d data)
        (unless (gethash (car d) .out-done.)
          (format out "~a" (cdr d))
          (setf (gethash (car d) .out-done.) t))))))

;;;
;;; show-undocumented
;;; list up undocumented, i.e. each keyword in *cafeobj-doc-db* which has no main in 
;;; its oldoc. 
;;;
(defparameter .todo. #~m/TODO/)

(defun show-undocumented (&rest ignore)
  (declare (ignore ignore))
  (let ((docs nil))
    (maphash #'(lambda (key oldoc)
                 (declare (ignore key))
                 (let* ((str (oldoc-main oldoc))
                        (doc (cl-ppcre:split "\\s+" str)))
                   (when (or (null doc)
                             (null (cdr doc))
                             (funcall .todo. str))
                     (push oldoc docs))))
             *cafeobj-doc-db*)
    (setq docs (sort docs #'string<= :key #'oldoc-key))
    (format t "~%The following commands/declarations/concepts are not yet documented.")
    (dolist (doc docs)
      (format t "~%** key   : ~s" (oldoc-key doc))
      (format t "~&   names : ~s" (oldoc-names doc)))))

;; oldoc-get-documents-by-category
;; returns the list of 
(defun oldoc-get-documents-by-category (cat)
  (let ((coms nil))
    (maphash #'(lambda (key oldoc) 
                 (let ((oldoc-cat (oldoc-category oldoc)))
                   (when (string-equal cat (symbol-name oldoc-cat))
                     (push (cons key oldoc) coms))))
             *cafeobj-doc-db*)
    (sort coms #'ob< :key #'car)))

;;
;; TOPLEVEL entry functions
;;
;; the following functions are called from the toplevel evaluation loop
;; in particular when one of the ? commands, and gendoc is called.
;
; oldoc-get-documentation
; returns the formatted string for display on the console
; returns nil if nothing found
(defun oldoc-get-documentation (question &key (main t) (example nil) (apropos nil) (related t))
  (if apropos
      (oldoc-search-all question)
    (let ((doc (oldoc-find-doc-entry question)))
      (if (not (listp doc))
          (oldoc-format-documentation doc :raw nil :main main :example example :related related)
        (progn 
          (if doc
              (format t "Did you mean one of ~a~%" doc))
          nil)))))

;; oldoc-list-categories
;;
(declaim (special .category-descriptions. .valid-com-categories.))

(defun oldoc-list-categories (cat)
  (unless cat
    (format t "** ======================================================================~%")
    (format t "COMMAND CLASSES:~%")
    (format t "'?com <class>' shows the list of commands classified by <class>.~2%")
    (format t "class~10Tdescription~%")
    (format t "-------------------------------------------------------------------------~%")
    (dolist (entry .category-descriptions.)
      (format t "~a~10T~a~%" (first entry) (second entry)))
    (return-from oldoc-list-categories nil))
  ;; gather commands
  (unless (member (car cat) .valid-com-categories. 
                  :test #'(lambda (x y) (string-equal x (symbol-name y))))
    (with-output-chaos-error ('invalid-category)
      (format t "System does not know the command class '~a'.~%" (car cat))
      (format t "Type '?cat' for the list of available class names.")))
  (let ((docs (oldoc-get-documents-by-category (car cat))))
    (unless docs
      (with-output-chaos-warning ()
        (format t "Sorry, the commands classified as '~a' not found." (car cat)))
      (return-from oldoc-list-categories nil))
    (format t "The list of commands classified as '~a'.~%" (car cat))
    (format t "Type '? <command-name>' for the online document of <command-name>.~%")
    (format t "==========================================================================")
    (do* ((dl docs (cdr dl))
          (doc (car dl) (car dl))
          (n 0 (1+ n)))
        ((endp dl))
      (let ((key (car doc))
            (desc (cdr doc)))
        (format t "~%~a~%  ~a" key (format-markdown (oldoc-title desc)))))))

;;; EOF
