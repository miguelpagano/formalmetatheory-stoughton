\begin{code}
open import Relation.Binary.Definitions
open import Relation.Binary.PropositionalEquality hiding ([_])

import Atom
module Alpha {Atom : Set} (_≟ₐ_ : Decidable {A = Atom} _≡_) (Χ : Atom.Chi _≟ₐ_) where
open Atom _≟ₐ_
open import Term _≟ₐ_ Χ hiding (_×_;∃)

open import Substitution  _≟ₐ_ Χ

open import Function
open import Data.Empty
open import Relation.Nullary
open import Data.Nat hiding (_*_)
open import Data.Product renaming (Σ to Σₓ)
open import Relation.Binary.PropositionalEquality as PropEq
  using (_≡_; _≢_; refl; sym; cong; cong₂; trans)
open PropEq.≡-Reasoning renaming (begin_ to begin≡_;_∎ to _◻)

infix  3 _∼α_ _∼αᵣ_
\end{code}


\begin{code}
data _∼α_ : Λ → Λ → Set where
  ∼v  : {x : Atom} → (v x) ∼α v x
  ∼·  : {M M' N N' : Λ} → M ∼α M' → N ∼α N'
      → M · N ∼α M' · N'
  ∼ƛ  : {M M' : Λ}{x x' y : Atom}
      → y # ƛ x M → y # ƛ x' M'
      → M ∙ (ι ≺+ (x , v y)) ∼α M' ∙ (ι ≺+ (x' , v y))
      → ƛ x M ∼α ƛ x' M'


data _∼αᵣ_ : Λ → Λ → Set where
  ∼v  : {x : Atom} → (v x) ∼αᵣ v x
  ∼·  : {M M' N N' : Λ} → M ∼αᵣ M' → N ∼αᵣ N'
      → M · N ∼αᵣ M' · N'
  ∼ƛ  : {M M' : Λ}{x x' y : Atom}
      → y # ƛ x M → y # ƛ x' M'
      → M ∙ᵣ (ιᵣ ≺+ (x , y)) ∼αᵣ M' ∙ᵣ (ιᵣ ≺+ (x' , y))
      → ƛ x M ∼αᵣ ƛ x' M'

αᵣ→α : ∀ M N → M ∼αᵣ N → M ∼α N
αᵣ→α .(v _) .(v _) ∼v = ∼v
αᵣ→α .(_ · _) .(_ · _) (∼· M∼αᵣN M∼αᵣN₁) = ∼· (αᵣ→α _ _ M∼αᵣN) (αᵣ→α _ _ M∼αᵣN₁)
αᵣ→α (ƛ z M) (ƛ w N) (∼ƛ {y = y} x x₁ M∼αᵣN)
  rewrite id-ren M _ _ (Σ∼Ren-upd ι ιᵣ M (ι∼Renιᵣ M) z y)
        | id-ren N _ _ (Σ∼Ren-upd ι ιᵣ N (ι∼Renιᵣ N) w y)
  = ∼ƛ {y = y} x x₁ (αᵣ→α _ _ M∼αᵣN)


α→αᵣ : ∀ M N → M ∼α N → M ∼αᵣ N
α→αᵣ .(v _) .(v _) ∼v = ∼v
α→αᵣ .(_ · _) .(_ · _) (∼· M∼αᵣN M∼αᵣN₁) = ∼· (α→αᵣ _ _ M∼αᵣN) (α→αᵣ _ _ M∼αᵣN₁)
α→αᵣ (ƛ z M) (ƛ w N) (∼ƛ {y = y} x x₁ M∼αᵣN)
  rewrite sym (id-ren M _ _ (Σ∼Ren-upd ι ιᵣ M (ι∼Renιᵣ M) z y))
        | sym (id-ren N _ _ (Σ∼Ren-upd ι ιᵣ N (ι∼Renιᵣ N) w y))
  = ∼ƛ {y = y} x x₁ (α→αᵣ _ _ M∼αᵣN)
\end{code}

\begin{code}
infix 1 _∼α_⇂_
_∼α_⇂_ : Σ → Σ → Λ → Set
σ ∼α σ' ⇂ M = (x : Atom) → x * M → σ x ∼α σ' x

lemmaι∼α⇂ : {M : Λ} → ι ∼α ι ⇂ M
lemmaι∼α⇂ {M} x _ = ∼v

lemma≺+∼α⇂ : {x : Atom}{M N P : Λ}{σ σ' : Σ} → σ ∼α σ' ⇂ M → N ∼α P → σ ≺+ (x , N) ∼α σ' ≺+ (x , P) ⇂ M
lemma≺+∼α⇂ {x} σ∼ασ'⇂M N~P y y*M with x ≟ₐ y
... | yes  _ = N~P
... | no   _ = σ∼ασ'⇂M y y*M
\end{code}

Freshness lemmas used in lemmaM∼M'→free lemmas

\begin{code}
lemmafree1 : {x y z : Atom}{M : Λ} → x ≢ z → z * M → z * (M ∙ (ι ≺+ (x , v y)))
lemmafree1 {x} {y} {z} {M} x≢z zfreeM = lemmafreeσ← {z} {M} (z , zfreeM , lemma)
  where lemma : z * ((ι ≺+ (x , v y)) z)
        lemma with x ≟ₐ z
        ... | yes x≡z = ⊥-elim (x≢z x≡z)
        ... | no  _   = *v

lemmafree2 : {x x' y z : Atom}{M M' : Λ} → y # (ƛ x M) → x ≢ z →
             z * (M' ∙ (ι ≺+ (x' , v y))) → z * M →
             x' ≢ z
lemmafree2 {x} {x'} {y} {z} {M} {M'} y#λxM x≢z zfreeM'ι≺+x'y zfreeM
  with lemmafreeσ→ {z} {M'} zfreeM'ι≺+x'y
... | w , wfreeM' , zfreeι≺+x'yw with x' ≟ₐ w
... | no  x'≢w with zfreeι≺+x'yw
lemmafree2 {x} {x'} {y} {z} {M} {M'} y#λxM x≢z zfreeM'ι≺+x'y zfreeM
    | .z , wfreeM' , zfreeι≺+x'yw
    | no  x'≢w
    | *v = λ x'≡z → x'≢w (trans (x'≡z) (sym refl))
lemmafree2 {x} {x'} {y} {z} {M} {M'} y#λxM x≢z zfreeM'ι≺+x'y zfreeM
    |  .x' , x'freeM' , x'freeι≺+x'yw | yes refl
    with y#λxM | x'freeι≺+x'yw
lemmafree2 {x} {x'} .{x} .{x} {M} {M'} y#λxM x≢y yfreeM'ι≺+x'y zfreeM
    |  .x' , x'freeM' , x'freeι≺+x'yw | yes refl
    | #ƛ≡ | *v = ⊥-elim (x≢y refl)
lemmafree2 {x} {x'} {y} .{y} {M} {M'} y#λxM x≢y yfreeM'ι≺+x'y zfreeM
    |  .x' , x'freeM' , x'freeι≺+x'yw | yes refl
    | #ƛ y#M  | *v = ⊥-elim ((lemma-free→¬# zfreeM) y#M) -- x' ≠ y

lemmafree3 : {x y z : Atom}{M : Λ} → z ≢ y → z * (M ∙ (ι ≺+ (x , v y))) → z * M
lemmafree3 {x} {y} {z} {M} z≢y zfreeMι≺+xy
  with lemmafreeσ→ {z} {M} zfreeMι≺+xy
... | w , wfreeM , zfreeι≺+xyw with x ≟ₐ w | zfreeι≺+xyw
lemmafree3 {x} {y} .{y} {M} y≢y yfreeMι≺+xy
    | w , wfreeM , yfreeι≺+xyw
    | yes x≡w | *v = ⊥-elim (y≢y refl)
lemmafree3 {x} {y} {z} {M} z≢y zfreeMι≺+xy
    | .z , zfreeM , _
    | no  x≡w | *v = zfreeM

lemmafree4 : {x y z : Atom}{M : Λ} → x ≢ z → z * M → y # (ƛ x M) → z ≢ y
lemmafree4 {x} .{x} {z} x≢z zfreeM #ƛ≡ = ≢-sym x≢z
lemmafree4 {x} {y} {z}  x≢z zfreeM (#ƛ y#M) with z ≟ₐ y
... | no  z≢y = z≢y
lemmafree4 {x} {y} .{y}  x≢y yfreeM (#ƛ  y#M)
    | yes refl = ⊥-elim ((lemma-free→¬# yfreeM) y#M)
\end{code}

\begin{code}
lemmaM∼M'→free→ : {M M' : Λ} → M ∼α M' →
                  (z : Atom) → z * M → z * M'
lemmaM∼M'→free→ ∼v                                 z zfreex
  = zfreex
lemmaM∼M'→free→ (∼· M∼M' N∼N')                     z (*·l zfreeM)
  = *·l (lemmaM∼M'→free→ M∼M' z zfreeM)
lemmaM∼M'→free→ (∼· M∼M' N∼N')                     z (*·r zfreeN)
  = *·r (lemmaM∼M'→free→ N∼N' z zfreeN)
lemmaM∼M'→free→ (∼ƛ {M} {M'} {x} {x'} {y}
                y#λxM y#λx'M' Mι≺+xy∼M'ι≺+x'y) z (*ƛ zfreeM x≢z)
  = *ƛ (lemmafree3 {x'} {y} {z} {M'} (lemmafree4 x≢z zfreeM y#λxM) lemma)
       (lemmafree2 {x} {x'} {y} {z} {M} {M'} y#λxM x≢z lemma zfreeM)
    where
    lemma : z * (M' ∙ (ι ≺+ (x' , v y)))
    lemma = lemmaM∼M'→free→ Mι≺+xy∼M'ι≺+x'y z (lemmafree1 x≢z zfreeM)
\end{code}

\begin{code}
lemmaM∼M'→free← : {M M' : Λ} → M ∼α M' →
                  (z : Atom) → z * M' → z * M
lemmaM∼M'→free← ∼v                                 z zfreex
  = zfreex
lemmaM∼M'→free← (∼· M∼M' N∼N')                     z (*·l zfreeM')
  = *·l (lemmaM∼M'→free← M∼M' z zfreeM')
lemmaM∼M'→free← (∼· M∼M' N∼N')                     z (*·r zfreeN')
  = *·r (lemmaM∼M'→free← N∼N' z zfreeN')
lemmaM∼M'→free← (∼ƛ {M} {M'} {x} {x'} {y}
                y#λxM y#λx'M' Mι≺+xy∼M'ι≺+x'y) z (*ƛ zfreeM' x'≢z)
  = *ƛ (lemmafree3 {x} {y} {z} {M} (lemmafree4 x'≢z zfreeM' y#λx'M') lemma)
       (lemmafree2 {x'} {x} {y} {z} {M'} {M} y#λx'M' x'≢z lemma zfreeM')
  where
  lemma : z * (M ∙ (ι ≺+ (x , v y)))
  lemma = lemmaM∼M'→free← Mι≺+xy∼M'ι≺+x'y z (lemmafree1 x'≢z zfreeM')
\end{code}

\begin{code}
lemmaM∼N# :  {M N : Λ}
             → M ∼α N
             → (z : Atom) → z # M → z # N
lemmaM∼N# {M} {N} M∼N z z#M with z #? N
... | yes z#N   = z#N
... | no  ¬z#N  = ⊥-elim ((lemma-free→¬# (lemmaM∼M'→free← M∼N z (lemma¬#→free ¬z#N))) z#M)
\end{code}
