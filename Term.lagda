\begin{code}
open import Relation.Binary.Definitions
open import Relation.Binary.PropositionalEquality hiding ([_])

import Atom
module Term {Atom : Set} (_≟ₐ_ : Decidable {A = Atom} _≡_) (Χ : Atom.Chi _≟ₐ_) where

open Atom _≟ₐ_


open import Data.Nat as Nat hiding (_*_)
open import Data.Nat.Properties
open import Data.Bool hiding (_∨_)
open import Data.Empty
open import Function
open import Function.Inverse hiding (sym;_∘_;map;id)
import Function.Equality as FE
open import Data.Sum hiding (map) renaming (_⊎_ to _∨_)
open import Data.Product renaming (Σ to Σₓ;map to mapₓ;_,_ to _∶_) public
open import Relation.Nullary
open import Relation.Nullary.Decidable hiding (map)
open import Relation.Binary hiding (Rel)
open import Relation.Binary.PropositionalEquality as PropEq renaming ([_] to [_]ᵢ)
open import Data.List hiding (any) renaming (length to length')
open import Algebra.Structures
open ≤-Reasoning
  renaming (begin_ to start_; _∎ to _◽; step-≡ to _≤⟨_⟩'_)

infix 6 _·_
infix 3 _#_
infix 1 _*_
\end{code}

\end{code}

%<*term>
\begin{code}
data Λ : Set where
  v    : Atom → Λ
  _·_  : Λ → Λ → Λ
  ƛ    : Atom → Λ → Λ
\end{code}
%</term>


%<*type>

\begin{code}
length : Λ → ℕ
length (v _)   = 1
length (M · N) = length M + length N
length (ƛ x M) = suc (length M)

length>0 : {M : Λ} → length M > zero
length>0 {v x}   = start
                    suc zero
                    ≤⟨ ≤-refl ⟩
                    suc zero
                   ◽
length>0 {M · N} = start
                      suc zero
                      ≤⟨ length>0 {M} ⟩
                      length M
                      ≤⟨ m≤m+n (length M) (length N) ⟩
                      length M + length N
                      ≤⟨ ≤-refl ⟩
                      length (M · N)
                   ◽
length>0 {ƛ x M} = start
                      suc zero
                      ≤⟨ s≤s z≤n ⟩
                      suc (suc zero)
                      ≤⟨ s≤s (length>0 {M}) ⟩
                      suc (length M)
                      ≤⟨ ≤-refl ⟩
                      length (ƛ x M)
                     ◽
\end{code}

Fresh variable

\begin{code}
data _#_ : Atom → Λ → Set where
  #v  :  {x y : Atom}         →  y ≢ x          →  x # v y
  #·  :  {x : Atom}{M N : Λ}  →  x # M → x # N  →  x # M · N
  #ƛ≡ :  {x : Atom}{M : Λ}                      →  x # ƛ x M
  #ƛ  :  {x y : Atom}{M : Λ}  →  x # M          →  x # ƛ y M
\end{code}

\begin{code}
_∼#_ : (M M' : Λ) → Set
_∼#_ M M' = (∀ x → x # M → x # M') × (∀ x → x # M' → x # M)
\end{code}

Variable Ocurr free in a term.

\begin{code}
data _*_ : Atom → Λ → Set where
  *v   :  {x : Atom}                           → x * v x
  *·l  :  {x : Atom}{M N : Λ} → x * M          → x * M · N
  *·r  :  {x : Atom}{M N : Λ} → x * N          → x * M · N
  *ƛ   :  {x y : Atom}{M : Λ} → x * M → y ≢ x  → x * ƛ y M

*-abs⁻ : ∀ {x y M} → x * (ƛ y M ) → (x * M) × x ≢ y
*-abs⁻ (*ƛ x*M y≢x) = x*M ∶ (≢-sym y≢x)
\end{code}

\begin{code}
_#?_ : Decidable _#_
x #? (v y) with y ≟ₐ x
... | yes y≡x = no (λ {(#v y≢x) → y≢x y≡x})
... | no  y≢x = yes (#v y≢x)
x #? (M · N) with x #? M | x #? N
... | yes x#M | yes  x#N = yes (#· x#M x#N)
... | yes x#M | no  ¬x#N = no (λ {(#· _ x#N) → ¬x#N x#N})
... | no ¬x#M | yes  x#N = no (λ {(#· x#M _)   → ¬x#M x#M})
... | no ¬x#M | no  ¬x#N = no (λ {(#· x#M _)   → ¬x#M x#M})
x #? (ƛ y M) with y | x ≟ₐ y
... | .x | yes refl = yes #ƛ≡
... | _  | no  x≢y with x #? M
...                | yes  x#M = yes (#ƛ x#M)
x #? (ƛ y M)
    | w  | no  x≢w | no  ¬x#M = no (aux x≢w ¬x#M)
  where aux : {x w : Atom} → x ≢ w → ¬ (x # M) →  x # ƛ w M → ⊥
        aux x≢w ¬x#ƛwM #ƛ≡         =  ⊥-elim (x≢w refl)
        aux x≢w ¬x#ƛwM (#ƛ x#ƛwM)  =  ⊥-elim (¬x#ƛwM x#ƛwM)

lemma¬#→free : {x : Atom}{M : Λ} → ¬ (x # M) → x * M
lemma¬#→free {x} {v y} ¬x#M with y ≟ₐ x
... | no  y≢x   = ⊥-elim (¬x#M (#v y≢x))
lemma¬#→free {x} {v .x} ¬x#M
    | yes refl  = *v
lemma¬#→free {x} {M · N} ¬x#MN with x #? M | x #? N
... | yes x#M | yes x#N = ⊥-elim (¬x#MN (#· x#M x#N))
... | yes x#M | no ¬x#N = *·r (lemma¬#→free ¬x#N)
... | no ¬x#M | yes x#N = *·l (lemma¬#→free ¬x#M)
... | no ¬x#M | no ¬x#N = *·r (lemma¬#→free ¬x#N)
lemma¬#→free {x} {ƛ y M} ¬x#λxM with y ≟ₐ x
... | no  y≢x with x #? M
... | yes x#M = ⊥-elim (¬x#λxM (#ƛ x#M))
... | no ¬x#M = *ƛ (lemma¬#→free ¬x#M) y≢x
lemma¬#→free {x} {ƛ .x M} ¬x#λxM
    | yes refl = ⊥-elim (¬x#λxM #ƛ≡)
--
lemma-free→¬# : {x : Atom}{M : Λ} → x * M →  ¬ (x # M)
lemma-free→¬# {x} {v .x} *v            (#v x≢x)
  = ⊥-elim (x≢x refl)
lemma-free→¬# {x} {M · N} (*·l xfreeM) (#· x#M x#N)
  = ⊥-elim ((lemma-free→¬# xfreeM) x#M)
lemma-free→¬# {x} {M · N} (*·r xfreeN) (#· x#M x#N)
  = ⊥-elim ((lemma-free→¬# xfreeN) x#N)
lemma-free→¬# {x} {ƛ .x M} (*ƛ xfreeM x≢x) #ƛ≡
  = ⊥-elim (x≢x refl)
lemma-free→¬# {x} {ƛ y M} (*ƛ xfreeM y≢x) (#ƛ x#M)
  = ⊥-elim ((lemma-free→¬# xfreeM) x#M)
--
lemma#→¬free : {x : Atom}{M : Λ} → x # M → ¬ (x * M)
lemma#→¬free x#M x*M = ⊥-elim ((lemma-free→¬# x*M) x#M)
\end{code}}

Sameness of free variables is an important relation between terms, which is defined as follows:

\begin{code}
_∼*_ : (M M' : Λ) → Set
M ∼* M' = (∀ x → x * M → x * M') × (∀ x → x * M' → x * M)

∼*ρ : Reflexive _∼*_
∼*ρ {M} = (λ _ → id) ∶ (λ _ → id)
\end{code}


\begin{code}
open import Relation Λ

dual-#-* : {R : Rel}{y : Atom} → (_#_ y) preserved-by R → (_*_ y) preserved-by (dual R)
dual-#-* {R} {y} #-pres-R {m} {m'} y*m m'Rm with y #? m'
... | yes y#m' = ⊥-elim (lemma-free→¬# y*m (#-pres-R {m'} {m} y#m' m'Rm))
... | no ¬y#m' = lemma¬#→free ¬y#m'

dual-*-# : {R : Rel}{y : Atom} → (_*_ y) preserved-by (dual R) → (_#_ y) preserved-by R
dual-*-# {R} {y} *-pres-R {m} {m'} y#m m'Rm with y #? m'
... | yes y#m' = y#m'
... | no ¬y#m' = ⊥-elim (lemma-free→¬# (*-pres-R (lemma¬#→free ¬y#m') m'Rm) y#m)
\end{code}
