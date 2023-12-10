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
open import Data.Empty
open import Data.Nat hiding (_*_)
open import Relation.Nullary
open import Relation.Binary hiding (Rel)
open import Function renaming (_∘_ to _∘f_)
open import Data.Product renaming (Σ to Σₓ)
open import Relation.Binary.PropositionalEquality as PropEq
  using (_≡_; _≢_; refl; sym; cong; cong₂; trans; setoid)
open PropEq.≡-Reasoning renaming (begin_ to begin≡_;_∎ to _◻)
open import Data.List hiding (any) renaming (length to length')
open import Data.List.Membership.Propositional
open import Data.List.Relation.Unary.Any hiding (map)
open import Data.List.Relation.Unary.Any.Properties
open import Data.List.Membership.Propositional.Properties
open import Data.List.Properties
\end{code}

\begin{code}
TermPrimIndType : {l : Level} (P : Λ → Set l) → Set l
TermPrimIndType P =
  (∀ a → P (v a))
  → (∀ M N → P M → P N → P (M · N))
  → (∀ M b → P M → P (ƛ b M))
  → ∀ M → P M

TermPrimInd : {l : Level}(P : Λ → Set l) → TermPrimIndType P
TermPrimInd P ha h· hƛ (v a)
  = ha a
TermPrimInd P ha h· hƛ (M · N)
  = h· M N (TermPrimInd P ha h· hƛ M) (TermPrimInd P ha h· hƛ N)
TermPrimInd P ha h· hƛ (ƛ a M)
  = hƛ M a (TermPrimInd P ha h· hƛ M)


module _   (l : Level) (P : Λ → Set l) (P-α-comp : ∀ M N → M ∼α N → P M → P N) where

  TermIndRen : Set l
  TermIndRen =
    (∀ a → P (v a))
    → (∀ M N → P M → P N → P (M · N))
    → (∀ M b → (∀ r → P (M ∙ᵣ r)) → P (ƛ b M))
    → ∀ M → P M


  IH-Strong : (∀ a → P (v a)) → (∀ M N → P M → P N → P (M · N)) → (∀ M b → (∀ r → P (M ∙ᵣ r)) → P (ƛ b M)) → ∀ M → (∀ r → P (M ∙ᵣ r))
  IH-Strong ha h-app h-abs (v x) r = ha (r x)
  IH-Strong ha h-app h-abs (M · M₁) r = h-app (M ∙ᵣ r) (M₁ ∙ᵣ r) (IH-Strong ha h-app h-abs M r) (IH-Strong ha h-app h-abs M₁ r)
  IH-Strong ha h-app h-abs (ƛ x M) r = h-abs (M ∙ᵣ r') y ih'
    where y = Chiᵣ (r , ƛ x M)
          y∉ = lemmaχ∉ (fv M)
          r' = r ≺+ (x , y)
          ih : ∀ r₁ → P (M  ∙ᵣ (r₁ ∘f r'))
          ih r₁ = IH-Strong ha h-app h-abs M (r₁ ∘f r')
          ih' : ∀ r₁ → P ((M  ∙ᵣ r') ∙ᵣ r₁)
          ih' r₁ = P-α-comp (M ∙ᵣ (r₁ ∘f r')) ((M ∙ᵣ r') ∙ᵣ r₁) b (ih r₁)
            where a = lemma∙compᵣ {M = M} {r'} {r₁}
                  b : (M ∙ᵣ (r₁ ∘f r')) ∼α ((M ∙ᵣ r') ∙ᵣ r₁)
                  b rewrite a = ∼ρ
          goal : (ƛ x M) ∙ᵣ r ≡ (ƛ y (M ∙ᵣ r'))
          goal = refl

  Ind⇒Strong : TermPrimIndType P → TermIndRen
  Ind⇒Strong ih ha h-app h-abs M = P-α-comp (M ∙ᵣ ιᵣ) M (∼σ lemma∙ιᵣ) (IH-Strong ha h-app h-abs M id)

  TermαIndPermType =
    (∀ a → P (v a))
    → (∀ M N → P M → P N →  P (M · N))
    → ∃ (λ as → (∀ M b  → b ∉ as
                      → P M
                      → P (ƛ b M)))
    → ∀ M → P M

  Strong⇒αInd : TermIndRen → TermαIndPermType
  Strong⇒αInd ind ha h-app h-abs = ind ha h-app (key-lemma' h-abs)
    where
      key-lemma' : ∃ (λ as → (∀ M b  → b ∉ as
                      → P M
                      → P (ƛ b M))) → (∀ M b → (∀ r → P (M ∙ᵣ r)) → P (ƛ b M))
      key-lemma' (cs , hip) M b f =
            P-α-comp (ƛ y (M ∙ᵣ (ιᵣ ≺+ (b , y)))) (ƛ b M)
              goal (hip (M ∙ᵣ (ιᵣ ≺+ (b , y))) y (∉-++⁻ʳ  y∉) (f (ιᵣ ≺+ (b , y))))
        where
        y = χ' (fv (ƛ b M) ++ cs)
        y∉ = lemmaχ∉ (fv (ƛ b M) ++ cs)
        id_ext = ∼σ (corollary4-2' {b} {y} {M} (lemma∉fv→# (∉-++⁻ˡ y∉)))
        h = id-ren M (ι ≺+ (b ∶ v y)) (ιᵣ ≺+ (b ∶ y)) (Σ∼Ren-upd _ _ M (ι∼Renιᵣ M) b y)
        goal :  ƛ y (M ∙ᵣ (ιᵣ ≺+ (b ∶ y))) ∼α ƛ b M
        goal rewrite h = id_ext


  TermαIndPerm_last : TermαIndPermType → TermPrimIndType P
  TermαIndPerm_last alphaInd ha h· habs = alphaInd ha h· ([] , (λ M b _ PM → habs M b PM))
\end{code}
