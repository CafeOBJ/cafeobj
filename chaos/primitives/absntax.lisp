;;;-*- Mode:LISP; Package:CHAOS; Base:10; Syntax:Common-lisp -*-
;;;
;;; Copyright (c) 2000-2015, Toshimi Sawada. All rights reserved.
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
#|==============================================================================
                                 System: CHAOS
                               Module: primitives
                               File: absntax.lisp
==============================================================================|#
#-:chaos-debug
(declaim (optimize (speed 3) (safety 0) #-GCL (debug 0)))
#+:chaos-debug
(declaim (optimize (speed 1) (safety 3) #-GCL (debug 3)))

;;; == DESCRIPTION =============================================================
;;; Here we define the representation of abstract syntax tree of Chaos program.
;;; The definition is also used for a basis of external interface with foreign
;;; systems.
;;;
;;; Chaos has no concrete syntax, only its abstract syntax is defined.
;;; Although we have no concrete syntax, we want some representation forms of
;;; Chaos program to enable us to do calculi about the program.
;;; The way we took for this purpose is to use a representation scheme which
;;; directly indicates abstract syntax tree of Chaos program.
;;; The tree is represented by the same notation of `list' in Lisp language.
;;; The nesting structure of list directly corresponds to the structure of the
;;; tree. Each list has a type tag as its first element indicating a type of a
;;; language construct. The tag is a symbol (in a sence of symbol in Lisp) whose
;;; print name begins with a letter `:' (a keyword symbol in Lisp jargon). cdr
;;; part of the list represents the other elements of the construct.
;;;
;;; -- Lexical Units.
;;; As for lexical units, such as identifier or numbers, we use generally
;;; accepted representation forms and do not abstract them. We are not so
;;; pedantic now. But this might be a limitation; possibly in some future, we
;;; might define lexical units in more abstract way.
;;; 
;;; Now there are only  FIVE types of lexical units:
;;;  (1) string : sequence of letters begins with a letter " and ends with ".
;;;               ex. " this is a string ". string is used for names
;;;               (identifiers) or for representing terms.
;;;               Instances of string appear at places in abstract syntax tree
;;;               which correspoind to <Identifier> or <Term> of abstract
;;;               syntax. 
;;;  (2) number : sequence of letters [1-9]+[0-9]* optionally prefixed by `-'.
;;;               Instances of number appear at the places corresponding
;;;               <Number> or <Natural> of abstract syntax.
;;;  (3) symbol : sequece of visible letters other than string or number.
;;;               most of the appearaces of symbols in trees are for
;;;               representing type tags, others are for representing <Symbol>
;;;               in the definition of abstract syntax.
;;;               A special symbol 'nil' can be used for representing
;;;               `not specified' value, indicating optional parts in abstract
;;;               syntax are omitted.
;;;  (4) parens : `(' and `)'. used for representing the structure of trees.
;;;               also used for representing a LIST OF XX. Note, there are no
;;;               ambiguity here, because a node representing some syntactic
;;;               category is always a list beginning with a keyword symbol.
;;;  (5) white-spaces : all of the invisible letters, these are treated as token
;;;             delimitters (except appearance in string).
;;;
;;; -- Representing Tree structure.
;;; As described already, structure is represented by a way similar to list
;;; notation of Lisp language. For an example, module importation of Chaos is
;;; defined as :
;;;   <ModuleImportation> ::= <Mode> <ModExp> [ <Parameter> ]
;;;
;;; One instace of this syntax may be represented by
;;;   (%import-decl :protecting (%modexp  "INT"))
;;; In tree representation
;;;                       :import-decl
;;;                         /      \
;;;                   :protecting  :modexp
;;;                                   |
;;;                                  "INT"
;;;
;;; where, :import-decl is a type tag which indicates this tree represents a
;;; <ModuleImportation>. :protecting is an example of usage of `symbol' in tree,
;;; in this case, it represents <Mode> of abstract syntax. We did not denote it
;;; like (%import-mode :protecting). This is because the abstract syntax of
;;; <Mode> is defined like <Mode> ::= <Protecting> | <Extending> | <Using> ...
;;; and <Protecting> ::= <Symbol> in Chaos, it is assumed that the concrete
;;; representation would be given when its concrete syntax is defined. In such a
;;; case, like this example, we give a concrete preresentation by symbols.
;;; (%modexp "INT") is an  instance of <ModExpr>, where :modexp is a type tag
;;; showing the node is of <Modexp>, and "INT" is an example of `string' in
;;; abstract syntax tree. The last element <Parameter> is defined as optional, 
;;; and it is omitted from the tree.
;;; 

;;;=============================================================================
;;; Chaos language expressions
;;;=============================================================================

;;; Every `evaluator' for declaration forms accepts the representation defined
;;; in this module (see "eval-ast.lisp" for detail).

;;; ** NOTE ********************************************************************
;;; To add a new language construct to CHAOS:
;;; (1) define abstract syntax (ast., -- internal form) of expressions needed for
;;; representing the new construct,
;;; (2) define evaluator(s) for ast defined in (1).
;;; The generic function `eval-ast' (see "eval-ast.lisp") accepts an ast and
;;; calls its evaluator, and returns the value (semantic object) as a result.
;;; The evaluator should be bound to a property ':eval' of the name of ast. The
;;; evaluator will accepts one argument `ast' the internal form to be evaluated.
;;; Run time environment is properly constructed when an evaluator is called,
;;; i.e., the global vairables such as *current-module*, *current-sort-order*,
;;; etc. are properly bound.
;;; The following macro `define-representation' provides an easy way to define
;;; a name of an ast, its structure, accessors, predicate, and constructors,
;;; and relates the evaluator of an ast defined via property :eval.
;;; ****************************************************************************


;;; AST ________________________________________________________________________
;;; common structure of abstract syntax.
;;;
;;; NOTE: definitions of lexical units ==>
;;;

(defterm seq (%ast)
  :visible (args)
  :eval eval-seq)

(defterm quote (%ast)
  :visible (obj)
  :eval eval-quote)

;;;=============================================================================
;;; SORT, SUBSORT RELATION, RECORD/CLASS SORT
;;;=============================================================================

;;; SORT-REF____________________________________________________________________
;;; Represents sort name. can have different meanings according to contexts.
;;; The default meaning (given by the evaluator of sort-ref) is the reference
;;; to an existing sort.
;;; sort-ref can appear in various context, for an instance, it will apper
;;; in sort declaration or subsort declaration. The former case, the meaning
;;; of sort-ref would be specifying a name of a sort to be declared, in the
;;; latter case, it would be a default meaning (denoting an existing sort),
;;; or a name of a sort to be declared.
;;;
;;; <SortRef> ::= <Identifier> [ <Qualifier> ]
;;;
;;; <Identifie> : string | symbol ; sort symbol
;;; <Qualifier> ::= <ModExpr>     ; qualification of sort symbol,
;;;                                 i.e., a module expression (optional).  
;;;               
;;; representation = (%sort-ref "name" <ModExpr>)
;;;
(defterm sort-ref (%ast)
  :visible (name &optional qualifier)
  :eval find-qual-sort                  ; the default meaning.
  :print print-sort-ref)

(defun may-be-error-sort-ref? (ref)
  (let ((name nil))
    (cond ((%is-sort-ref ref) (setq name (%sort-ref-name ref)))
          ((symbolp ref) (setq name (string ref)))
          ((stringp ref) (setq name ref))
          (t (with-output-panic-message ()
               (format t "invalid sort reference ~a" ref)
               (chaos-error 'panic))))
    (eql #\? (schar name 0))))
           
;;; * NOTE *
;;; 1. As described above, the meaning of `sort-ref' is overloaded, this is
;;; because of a feature of CafeOBJ for relaxing a restriction of subsort
;;; declaration.
;;; 2. In declaring sort or subsort relation, `sort-ref' can be represented
;;; by an ast `sort-ref', a simple string or a symbol possibly be qualified
;;; by a module expression. This gives some flexibility to the parsing process
;;; but is rather dirty. Evaluators of sort declaration,
;;; subsort declaration, and calss/record sort declaration must be careful about
;;; it.

;;; SORT DECLARATION____________________________________________________________
;;; Sort declaration form.
;;; <SortDeclaration> ::= string | symbol | sort-ref
;;; representation = (%sort-decl name)
;;;
(defterm sort-decl (%ast)
  :visible (name                        ; one of string, symbol,
                                        ; ast `:sort-ref'.
            &optional hidden)           ; non-nil iff hidden sorts.
  :eval declare-sort
  :print print-sort-decl)

;;; BSORT DECLARATION___________________________________________________________
;;; builtin sort declaration form.
;;;  token-predicate : function name, type = symbol, possibly be nil.
;;;  term-creator    : function name, type = symbol, possibly be nil.
;;;  term-printer    : function name, type = symbol, possibly be nil.
;;;  term-predicate  : function name, type = symbol, possibly be nil.
;;;
(defterm bsort-decl (%ast)
  :visible (name token-predicate term-creator
                 term-printer term-predicate
                 hidden)
  :eval declare-bsort
  :print print-bsort-decl)

;;; SUBSORT DECLARATION_________________________________________________________
;;; Subsort relation declaration form.
;;;  sort-realtion : list of sort-name with special order marker ':< in it.
;;; ex. (hidden-flag . (%sort-ref "Foo") :< (%sort-ref "Bar") :< (%sort-ref "Baz") )
;;;
(defterm subsort-decl (%ast)
  :visible (&rest sort-relation)
  :eval declare-subsort
  :print print-subsort-decl)

;;; PRINCIPAL SORT DECLARATION__________________________________________________
;;;
(defterm psort-decl (%ast)
  :visible (sort)
  :eval declare-psort
  :print print-psort-decl)

;;; ATTRIBUTE MAP_______________________________________________________________
;;; Used for representing attribute renaming of record/class inheritance.
;;; No own evaluator.
;;;   source : name of attribute to be renamed, type = string | symbol
;;;   target : gives the new name, type = string | symbol
;;;
(defterm attr-rename (%ast)
  :visible (source target)
  )

;;; Record/Class ATTRIBUTE_____________________________________________________
;;; Represents record/class sort's attribute.
;;;  name    : attribute name, type = string.
;;;  sort    : attribute's sort, type = one of string, sort-name, symbol
;;;  default : attribute's default value, type = string or list of string.
;;; No evaluator.
;;;
(defterm slot (%ast)
  :visible (name sort default))

;;; Super______________________________________________________________________
;;; Represents super record/class.
;;;  sort    : super sort, type = one of string, sort-name, symbol
;;;  renames : list of attribute rename map, type = attr-rename, possibly be nil.
;;; No evaluator.
;;;
(defterm super (%ast)
  :visible (sort &optional renames))

;;; Record Declaration _________________________________________________________
;;; Represents record sort declaration form.
;;;  name       : name of record sort, type = one of string, symbol
;;;  supers     : list of super sorts, type = list of super, possibly be nil.
;;;  attributes : list of attributes, type = list of slot, possibly be nil.
;;;
(defterm record-decl (%ast)
  :visible (name supers attributes &optional hidden)
  :eval declare-record)

;;; Class Declaration __________________________________________________________
;;; Represents class sort declaration form.
;;;  the structure is just the same as of record declaration.
;;;
(defterm class-decl (%ast)
  :visible (name supers attributes &optional hidden)
  :eval declare-class)



;;;=============================================================================
;;; Operator, Method
;;;=============================================================================

;;; OPERATOR REFERENCE__________________________________________________________
;;; used for refer an operator.
;;;  name     : a list of string representing syntax.
;;;  module   : qualifier(module expression) representing context.
;;;  num-args : natural number indicating the number of arguments.
;;;
(defterm opref (%ast)
  :visible (name &optional module num-args)
  :eval find-qual-operators
  :print print-opref)

;;; OPERATOR/METHOD ATTRIBUTES__________________________________________________
;;;  theory : list of theory specifiers. A specifier is one of ':assoc, ':comm,
;;;           ':idem, (:id term), (:idr term), where term is either a string, or
;;;           list of tokens.
;;;  assoc  : associativity specifier, one of ':l-assoc, ':rassoc, possibly nil.
;;;  prec   : precedence specifier, type = (integer 0 ... 127). possibly nil.
;;;  strat  : rewrite strategy, type = list of integer. possibly nil.
;;;  memo   : meoization spcifier, type = or nil t.
;;;  constr : flag, only meaningfull for methods, type = or nil t.
;;;           t iff the method is a constructor.
;;;
;;;  Has NO own evaluator.
;;;
(defterm opattrs (%ast)
  :visible (theory assoc prec strat memo constr coherent &optional meta-demod)
  :print print-opattrs-ast)

;;; OPERATOR DECLARATION________________________________________________________
;;; name       : name of an operator. the name is a list of string, argument
;;;              place marker is specified by "_".
;;; arity      : list of sort (sort reference). possibly nil.
;;; coarity    : sort (sort reference).
;;; attributes : attributes, type = opattrs (see above), possibly nil.
;;;
(defterm op-decl (%ast)
  :visible (name arity coarity attribute &optional hidden)
  :eval declare-operator
  :print print-op-decl-ast)

;;; ATTRIBUTE DECLARATION_______________________________________________________
;;; opref      : operator reference, see opref above.
;;; attributes : attribute to to be declared, type = opattrs.
;;;
#||
(defterm opattr-decl (%ast)
  :visible (opref attribute)
  :eval declare-operator-attributes
  :print print-opattr-decl)
||#

;;; METHOD REFERENCE, *NOTE* NOT USED.
;;; name       : operator name.
;;; arity      : list of sort reference, possibly nil.
;;; coarity    : sort reference.
;;; module     : qualifier.
;;;
(defterm meth-ref (%ast)
  :visible (name arity coarity &optional module))



;;;=============================================================================
;;; AXIOMS, VARIABLE
;;;=============================================================================

;;; Variable Declaration________________________________________________________
;;; names  : list of name of variable, type = list of string.
;;; sort   : sort, type = sort (sort-reference).
;;;
(defterm var-decl (%ast)
  :visible (names sort)
  :eval declare-variable
  :print print-var-decl)

(defterm pvar-decl (%ast)
  :visible (names sort)
  :eval declare-pvariable
  :print print-pvar-decl)

;;; LET Declaration____________________________________________________________
;;; 
(defterm let (%ast)
  :visible (sym                         ; name
            value)                      ; value (pre-term).
  :eval eval-let
  :print print-let-decl)

;;; MACRO Declaration__________________________________________________________
;;;
(defterm macro (%ast)
  :visible (lhs rhs)
  :eval eval-macro
  :print print-macro-decl)

;;; Axiom-DECL_________________________________________________________________
;;; can be used for both denoting axiom and axiom declaration form. the bound
;;; evaluator consider the form as axiom declaration form.
;;;
;;; type    : one of ':equation, or ':rule. type = symbol
;;; labels  : list of labels, type = list of symbol
;;; lhs     : left hand side, type = or list of tokens, string.
;;; rhs     : right hand side, type = or list of tokens, string.
;;; cond    : condition, type = or list of tokens, string. possibly be nil.
;;; behavioural : non-nil symbol iff the axiom is behavioural
;;;
(defterm axiom-decl (%ast)
  :visible (type labels lhs rhs cond &optional behavioural)
  :eval declare-axiom
  :print print-axiom-decl-form)

;;; Axiom Reference_____________________________________________________________
;;; representing a reference to axioms (a name can be represents multiple
;;; axioms).
;;;  name   : a name of an axiom. type = string or symbol.
;;;  module : module expression, qualifier.
;;;
(defterm ax-ref (%ast)
  :visible (name &optional module)
  :eval find-qual-axiom)

;;; EQUATION REFERENCE
;;;
(defterm eq-ref (%ast)
  :visible (name &optional module)
  :eval find-qual-equation)

;;; RULE REFERENCE
;;;
(defterm rl-ref (%ast)
  :visible (name &optional mdoule)
  :eval find-qual-rl)

;;; REWRITE RULE REFERENCE
;;;
(defterm rrule-ref (%ast)
  :visible (name &optional module)
  :eval find-qual-rrule)

;;;=============================================================================
;;;                            MODULE IMPORTATION
;;;=============================================================================

;;; IMPORT DECLARATION__________________________________________________________
;;;  mode : import mode, one of ':protecting, ':extending, ':using, ':including
;;;  module : module to be imported, modexp
;;;  parameter : local name acting as formal parameter name, type = string.
;;;
(defterm import (%ast)
  :visible (mode module &optional parameter alias)
  :eval eval-import-modexp
  :print print-import-decl)

;;;=============================================================================
;;;                         SIGNATURE, AXIOM, MODULE
;;;=============================================================================

;;; SIGNATURE___________________________________________________________________
;;; Represents both signature & signature declaration.
;;;
(defterm signature (%ast)
  :visible (sorts sort-relations operators opattrs))

;;; AXIOM SET___________________________________________________________________
;;;  variables : list of variables
;;;  equations : list of equations
;;;  rules     : list of rules
;;;
(defterm axioms (%ast)
  :visible (variables equations rules))

;;; MODULE DECLARATION__________________________________________________________
;;;  name     : name of the module, string or modexp.
;;   kind     : one of :theory, :object, :module
;;;  type     : one of :system, :user, :hard
;;;  elements : list of declaration forms
;;;
(defterm module-decl (%ast)
  :visible (name kind type &rest elements)
  :eval declare-module
  :print print-module-decl)

;;; VIEW DECLARATION____________________________________________________________
;;; name      : name of the view, string
;;; view      : view
;;;
(defterm view-decl (%ast)
  :visible (name view)
  :eval declare-view)

;;; EOF
