\begin{code}
open import Relation.Binary.Definitions using (Decidable)
open import Relation.Binary.PropositionalEquality using (_≡_)
open import Level
import Atom
module InductionPrinciples {Atom : Set} (_≟ₐ_ : Decidable {A = Atom} _≡_) (Χ : Atom.Chi _≟ₐ_) where
open Atom _≟ₐ_
open Chi Χ
open import Term _≟ₐ_ Χ hiding (_×_;∃)
open import Substitution _≟ₐ_ Χ
open import Alpha _≟ₐ_ Χ
open import SubstitutionLemmas _≟ₐ_ Χ
open import Relation.Nullary
open import Relation.Binary hiding (Rel)
open import Function renaming (_∘_ to _∘f_)
open import Data.Product
open import Relation.Binary.PropositionalEquality as PropEq
  using (_≡_; _≢_; refl; sym; cong; cong₂; trans)
open import Data.List
open import Data.List.Membership.Propositional
\end{code}

We present the induction principles exactly as in the paper.
\begin{code}
StructuralInduction : {l : Level} → (P : Λ → Set l) → Set l
StructuralInduction {l} P = 
  (∀ a → P (v a))
  → (∀ M N → P M → P N → P (M · N))
  → (∀ M b → P M → P (ƛ b M))
-----------------------------------
  → ∀ M → P M

structural-induction : {l : Level} → ∀ P → StructuralInduction {l} P
structural-induction P h-at h-app h-abs (v a)
  = h-at a
structural-induction P h-at h-app h-abs (M · N)
  = h-app M N (structural-induction P h-at h-app h-abs M) (structural-induction P h-at h-app h-abs N)
structural-induction P h-at h-app h-abs (ƛ a M)
  = h-abs M a (structural-induction P h-at h-app h-abs M)

StrongRenamingInduction : {l : Level} (P : Λ → Set l) → Set l
StrongRenamingInduction P =
  (∀ a → P (v a))
  → (∀ M N → P M → P N → P (M · N))
  → (∀ M b → (∀ r → P (M ∙ᵣ r)) → P (ƛ b M))
--------------------------------------------
  → ∀ M → P M


AlphaInduction : {l : Level} (P : Λ → Set l) → Set l
AlphaInduction P =
  (∀ a → P (v a))
  → (∀ M N → P M → P N →  P (M · N))
  → ∃ (λ as → (∀ M b  → b ∉ as
                    → P M
                    → P (ƛ b M)))
------------------------------------
  → ∀ M → P M
\end{code}

\begin{code}

Structural⇒Renaming : ∀ {l} → (∀ P → StructuralInduction {l} P) →
                      ∀ (P : Λ → Set l) → (P Respects (_∼αᵣ_)) →
                      StrongRenamingInduction P
Structural⇒Renaming {l} struct-ind P P-α-comp h-at h-app h-abs M =
   P-α-comp (α→αᵣ (∼σ lemma∙ιᵣ)) (stronger-ind P P-α-comp h-at h-app h-abs M id)
     where
     stronger-ind : ∀ (P : Λ → Set l) → (P-α-comp : P Respects (_∼αᵣ_)) →
         (∀ a → P (v a)) →
         (∀ M N → P M → P N → P (M · N)) →
         (∀ M b → (∀ r → P (M ∙ᵣ r)) → P (ƛ b M)) →
         ∀ M r → P (M ∙ᵣ r)
     stronger-ind P P-α-comp h-at h-app h-abs =  struct-ind (λ M → ∀ r → P (M ∙ᵣ r) )
                                               (λ a r → h-at (r a))
                                                (λ M N ihM ihN r → h-app (M ∙ᵣ r) (N ∙ᵣ r) (ihM r) (ihN r))
                                                h-abs'
        where
        h-abs' : (M : Λ) (x : Atom) → ((r' : Ren) → P (M ∙ᵣ r')) → (r : Ren) → P (ƛ x M ∙ᵣ r)
        h-abs' M x ihM r = h-abs (M ∙ᵣ r') y ih'
           where
           y = Chiᵣ (r , ƛ x M)
           y∉ = lemmaχ∉ (fv M)
           r' = r ≺+ (x , y)
           ih' : ∀ r₁ → P ((M  ∙ᵣ r') ∙ᵣ r₁)
           ih' r₁ rewrite lemma∙compᵣ {M} {r'} {r₁} = P-α-comp (α→αᵣ ∼ρ) (ihM (r₁ ∘f r'))

Strong⇒AlphaInduction : ∀ {l} → (∀ P → StrongRenamingInduction P) →
                        (∀ (P : Λ → Set l) → (P Respects (_∼αᵣ_)) → AlphaInduction P)
Strong⇒AlphaInduction strong-ind P P-α-comp h-at h-app h-abs = strong-ind P h-at h-app (key-lemma h-abs)
  where
  key-lemma : ∃ (λ as → (∀ M b  → b ∉ as
                  → P M
                  → P (ƛ b M))) → (∀ M b → (∀ r → P (M ∙ᵣ r)) → P (ƛ b M))
  key-lemma (cs , hip) M b hipM = P-α-comp goal (hip (M ∙ᵣ (ιᵣ ≺+ (b , y))) y (∉-++⁻ʳ  y∉) (hipM (ιᵣ ≺+ (b , y))))
    where
    y = χ' (fv (ƛ b M) ++ cs)
    y∉ = lemmaχ∉ (fv (ƛ b M) ++ cs)
    Mιby≡Mιᵣby = id-ren {M} (Σ∼Ren-upd {M = M} (ι∼Renιᵣ M) b y)
    goal :  ƛ y (M ∙ᵣ (ιᵣ ≺+ (b ∶ y))) ∼αᵣ ƛ b M
    goal rewrite Mιby≡Mιᵣby = α→αᵣ (∼σ (corollary4-2' {b} {y} {M} (lemma∉fv→# (∉-++⁻ˡ y∉))))


AlphaInduction⇒Structural : ∀ {l} → (∀ P → AlphaInduction P) → (∀ P → StructuralInduction {l} P)
AlphaInduction⇒Structural α-ind P h-at h-app h-abs = α-ind P h-at h-app ([] , (λ M b _ PM → h-abs M b PM))
\end{code}
