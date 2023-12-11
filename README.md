# Alpha-Structural Induction and Recursion for the Lambda Calculus in Constructive Type Theory Using Simple Renaming

In the context of Constructive Type Theory, we investigate the use of simple,
not necessarily injective, renaming for the justification of a principle of
induction and recursion for a variant of lambda calculus in its original syntax
(i.e., with only one sort of names) that allows to work modulo α-conversion and
implement the Barendregt variable convention. We conclude that, for predicates
preserved under α- conversion, the principle in question is equivalent to simple
structural induction and recursion. The corresponding proofs have been checked
in the system Agda.

The main file is [InductionPrinciples](InductionPrinciples.lagda).

This formalization is an extension of (an updated version of)
https://github.com/ernius/formalmetatheory-stoughton . I, Miguel Pagano, updated
the library in order to make it compatible with Agda 2.6.4 and the standard
library v. 1.7.2. I've removed all the modules not relevant for the current 
formalization.

# Authors

* Álvaro Tasistro (Universidad ORT Uruguay)
* Nora Szasz (Universidad ORT Uruguay)
* Ernesto Copello (Universidad ORT Uruguay)
* Miguel Pagano (FAMAF - Universidad Nacional de Córdoba)
