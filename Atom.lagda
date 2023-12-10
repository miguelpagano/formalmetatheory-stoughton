\begin{code}
open import Relation.Binary.Definitions
open import Relation.Binary.PropositionalEquality

module Atom {Atom : Set} (_≟ₐ_ : Decidable {A = Atom} _≡_) where

open import Data.List
open import Data.List.Membership.Propositional
open import Data.List.Relation.Binary.Subset.Propositional
open import Data.Nat
open import Data.Product renaming (_×_ to _∧_)
open import Data.Sum renaming (_⊎_ to _∨_)
open import Data.Sum
open import Data.Empty
open import Relation.Nullary
open import Relation.Nullary.Negation
open import Relation.Binary.PropositionalEquality as PropEq
open PropEq.≡-Reasoning renaming (begin_ to begin≡_;_∎ to _□)

record Chi : Set where
  field
    χ' : List Atom → Atom
    lemmaχ∉ : (xs : List Atom) → χ' xs ∉ xs
    lemmaχaux⊆ : (xs ys : List Atom) → xs ⊆ ys → ys ⊆ xs → χ' xs ≡ χ' ys

_-ₐ_ : List Atom → Atom → List Atom
xs -ₐ x = filter ((λ y → ¬? (x ≟ₐ y))) xs
\end{code}
