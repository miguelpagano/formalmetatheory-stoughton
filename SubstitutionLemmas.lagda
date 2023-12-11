\begin{code}
open import Relation.Binary.Definitions using (Decidable)
open import Relation.Binary.PropositionalEquality using (_≡_)

import Atom
module SubstitutionLemmas {Atom : Set} (_≟ₐ_ : Decidable {A = Atom} _≡_) (Χ : Atom.Chi _≟ₐ_) where
open Atom _≟ₐ_
open Chi Χ
open import Term _≟ₐ_ Χ hiding (_×_;∃)
open import Substitution _≟ₐ_ Χ
open import Alpha _≟ₐ_ Χ
open import NaturalProp
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

Lemma 3.1 (v) Stougthton

\begin{code}
lemmaσ≡σ'→Mσ≡Mσ'  : {M : Λ}{σ σ' : Σ}
                  → σ ≅ σ' ⇂ M
                  → M ∙ σ ≡ M ∙ σ'
lemmaσ≡σ'→Mσ≡Mσ' {v x}   {σ} {σ'} (_ , f)
  = f x *v
lemmaσ≡σ'→Mσ≡Mσ' {M · N} {σ} {σ'} (_ , f)
  = cong₂ _·_
          (lemmaσ≡σ'→Mσ≡Mσ' {M} {σ} {σ'} (∼*ρ , (λ x xfreeM → f x (*·l xfreeM))))
          (lemmaσ≡σ'→Mσ≡Mσ' {N} {σ} {σ'} (∼*ρ , (λ x xfreeN → f x (*·r xfreeN))))
lemmaσ≡σ'→Mσ≡Mσ' {ƛ x M} {σ} {σ'} (_ , f)
  with Chi' (σ , ƛ x M) | Chi' (σ' , ƛ x M) |
       χ-lemma3 σ σ' (ƛ x M) (ƛ x M) (λ x x*M → ((lemma σ σ' f x x*M) , (lemma σ' σ f2 x x*M))) ∼*ρ
  where
  lemma : (σ σ' : Σ) → ((y : Atom) → y * (ƛ x M) → σ y ≡ σ' y) → (z : Atom) → z * ƛ x M → (y : Atom) → y * σ z → y * σ' z
  lemma σ σ' f z zfreeλxM y yfreeσz rewrite f z zfreeλxM = yfreeσz
  f2 : (y : Atom) → y * (ƛ x M) → σ' y ≡ σ y
  f2 y yfreeλxM = sym (f y yfreeλxM)
... | y | .y | refl
  =  cong (ƛ y) (lemmaσ≡σ'→Mσ≡Mσ' {M} {σ ≺+ (x , v y)} {σ' ≺+ (x , v y)} (∼*ρ , lemma))
  where
  lemma : (z : Atom) → z * M → (σ ≺+ (x , v y)) z ≡ (σ' ≺+ (x , v y)) z
  lemma z zfreeM with x ≟ₐ z
  ... | yes _   = refl
  ... | no  x≢z = f z (*ƛ zfreeM x≢z)
\end{code}

\begin{code}
lemma1 : {M : Λ}{σ σ' : Σ} → σ ≅ σ' ⇂ M → M ∙ σ ≡ M ∙ σ'
lemma1 = lemmaσ≡σ'→Mσ≡Mσ'
--
lemmaMι≺+x,x : {x : Atom}{M : Λ} → M ∙ (ι ≺+ (x , v x)) ≡ M ∙ ι
lemmaMι≺+x,x {x} {M} = lemmaσ≡σ'→Mσ≡Mσ' {M} (prop6 {ι ≺+ (x , v x)} {ι} (lemmaσ≺+x,x≅σ {x}))
\end{code}

\begin{code}
lemmaσ∘≺+ : (M N : Λ)(σ σ' : Σ)(x y : Atom)
       → y #⇂ (σ , ƛ x M)
       → (w : Atom) → w * M
       → ((σ' ≺+ (y , N)) ∘ (σ ≺+ (x , v y))) w ≡ ((σ' ∘ σ) ≺+ (x , N)) w
lemmaσ∘≺+ M N σ σ' x y y#⇂σ,ƛxM w wfreeM with x ≟ₐ w
... | no  x≢w = begin≡
                   ((σ w) ∙ (σ' ≺+ (y , N)))
                   ≡⟨ lemmaσ≡σ'→Mσ≡Mσ' {σ w} {σ' ≺+ (y , N)} {σ'} (∼*ρ , lemma) ⟩
                   (σ w) ∙ σ'
                ◻
    where
    lemma : (u : Atom) → u * σ w → (σ' ≺+ (y , N)) u ≡ σ' u
    lemma u ufreeσw with y#⇂σ,ƛxM w (*ƛ wfreeM x≢w)
    ... | y#σw with y ≟ₐ u
    ...        | no  _    = refl
    lemma .y yfreeσw | y#σw
               | yes refl = ⊥-elim ((lemma-free→¬# yfreeσw) y#σw)
... | yes x≡w with y ≟ₐ y
...           | yes y≡y = refl
...           | no  y≢y = ⊥-elim (y≢y refl)
--
lemmaχσ∘≺+ : (M N : Λ)(σ σ' : Σ)(x : Atom)
       → (w : Atom) → w * M
       → ((σ' ≺+ (Chi' (σ , ƛ x M) , N)) ∘ (σ ≺+ (x , v (Chi' (σ , ƛ x M))))) w ≡ ((σ' ∘ σ) ≺+ (x , N)) w
lemmaχσ∘≺+ M N σ σ' x = lemmaσ∘≺+ M N σ σ' x (Chi' (σ , ƛ x M)) (χ-lemma2 σ (ƛ x M))
\end{code}


\begin{code}
lemma· : {M : Λ}{σ σ' : Σ} → (M ∙ σ) ∙ σ' ≡ M ∙ (σ' ∘ σ)
lemma· {v x}   {σ} {σ'} = refl
lemma· {M · N} {σ} {σ'} = cong₂ _·_ (lemma· {M}) (lemma· {N})
lemma· {ƛ x M} {σ} {σ'}
  = begin≡
      ((ƛ x M) ∙ σ) ∙ σ'
      ≡⟨ refl ⟩
      (ƛ y (M ∙ (σ ≺+ (x , v y)))) ∙ σ'
      ≡⟨ refl ⟩
      ƛ y' ((M ∙ (σ ≺+ (x , v y))) ∙ (σ' ≺+ (y , v y')))
      ≡⟨ cong (λ M → ƛ y' M) (lemma· {M} {σ ≺+ (x , v y)} {σ' ≺+ (y , v y')}) ⟩
      ƛ y' (M ∙ ((σ' ≺+ (y , v y')) ∘ (σ ≺+ (x , v y))))
      ≡⟨ cong (λ M → ƛ y' M) (lemmaσ≡σ'→Mσ≡Mσ' {M} {(σ' ≺+ (y , v y')) ∘ (σ ≺+ (x , v y))} {(σ' ∘ σ) ≺+ (x , v y')} ((∼*ρ , lemmaχσ∘≺+ M (v y') σ σ' x))) ⟩
      ƛ y' (M ∙ ((σ' ∘ σ) ≺+ (x , v y')))
      ≡⟨ cong (λ z → ƛ z (M ∙ ((σ' ∘ σ) ≺+ (x , v z)))) lemma ⟩
      ƛ z (M ∙ ((σ' ∘ σ) ≺+ (x , v z)))
      ≡⟨ refl ⟩
      (ƛ x M) ∙ (σ' ∘ σ)
   ◻
  where
  y = Chi' (σ , ƛ x M)
  y' = Chi' (σ' , ƛ y (M ∙ (σ ≺+ (x , v y))))
  z = Chi' (σ' ∘ σ , ƛ x M)
  -- lemma 3.1 (viii) Stoughton
  lemma3→ :  (y' : Atom) → ∃ (λ x' →  (x' * ƛ y (M ∙ (σ ≺+ (x , v y)))) × (y' * σ' x')) →
             ∃ (λ u → (u * ƛ x M) × (y' * (σ' ∘ σ) u))
  lemma3→ y' (x' , (*ƛ x'freeMσ≺+xy y≢x') , y'freeσ'x') with lemmafreeσ→ {x'} {M} x'freeMσ≺+xy
  ... | u , ufreeM , x'freeσ≺+xyu with x ≟ₐ u
  ... | no  x≢u =  u , *ƛ ufreeM x≢u ,  lemmafreeσ← {y'} {σ u} {σ'} (x' , x'freeσ≺+xyu , y'freeσ'x')
  lemma3→ y' (.y , (*ƛ yfreeMσ≺+xy y≢y) , y'freeσ'y )
      | .x , xfreeM , *v
      | yes refl = ⊥-elim (y≢y refl)
  lemma3← :  (y' : Atom) → ∃ (λ x' → (x' * ƛ x M) × (y' * (σ' ∘ σ) x')) →
             ∃ (λ u → (u * ƛ y (M ∙ (σ ≺+ (x , v y)))) × (y' * σ' u))
  lemma3← y' (x' , (*ƛ x'freeM x≢x') , y'freeσσ'x') with lemmafreeσ→ {y'} {σ x'} {σ'} y'freeσσ'x'
  ... | u , ufreeσx' , y'freeσ'u with lemmafreeσ← {u} {M} {σ ≺+ (x , v y)} (x' , x'freeM  , lemma)
     where lemma : u * ((σ ≺+ (x , v y)) x')
           lemma with x ≟ₐ x'
           ... | yes x≡x' = ⊥-elim (x≢x' x≡x')
           ... | no  _    = ufreeσx'
  ... | ufreeMσ≺+xy = u , *ƛ ufreeMσ≺+xy (y≢u ufreeσx') , y'freeσ'u
     where y≢u : {u : Atom} → u * (σ x') →  y ≢ u
           y≢u {u} ufreeσx' with u | ufreeσx' | y ≟ₐ u
           ... | .y | yfreeσx' | yes refl
             = ⊥-elim ((lemma-free→¬# yfreeσx') ((χ-lemma2 σ (ƛ x M)) x' (*ƛ x'freeM x≢x')))
           ... | _  | _        | no y≢up  =  y≢up
  lemma : y' ≡ z
  lemma =  χ-lemma4 σ' (σ' ∘ σ) (ƛ y (M ∙ (σ ≺+ (x , v y)))) (ƛ x M)
                    (lemma3→ , lemma3←)
\end{code}

\begin{code}
lemma≺+ : {x z : Atom}{M N : Λ}{σ : Σ} → z # (ƛ x M) → M ∙ (σ ≺+ (x , N)) ≡ (M ∙ (ι ≺+ (x , v z))) ∙ (σ ≺+ (z , N))
lemma≺+ {x} {z} {M} {N} {σ} z#λxM rewrite lemma· {M} {ι ≺+ (x , v z)} {σ ≺+ (z , N)}
  = lemmaσ≡σ'→Mσ≡Mσ' {M} {σ ≺+ (x , N)} {(σ ≺+ (z , N)) ∘ (ι ≺+ (x , v z))} (∼*ρ , lemma)
  where
  lemma : (w : Atom) → w * M → (σ ≺+ (x , N)) w ≡ (((σ ≺+ (z , N)) ∘ (ι ≺+ (x , v z))) w) -- este me sirve ???
  lemma w wfreeM with x ≟ₐ w
  ... | no x≢w  with z ≟ₐ w
  ... | no _    = refl
  ... | yes z≡w = ⊥-elim ((z≢w x z w M z#λxM wfreeM x≢w) z≡w)
    where
    z≢w : (x z w : Atom)(M : Λ) → z # (ƛ x M) → w * M → x ≢ w  → z ≢ w
    z≢w x .x w M #ƛ≡ wfreeM x≢w = x≢w
    z≢w x z w M (#ƛ  z#M) wfreeM x≢w with z ≟ₐ w
    ... | no z≢w = z≢w
    z≢w x z .z M (#ƛ  z#M) zfreeM x≢w
        | yes refl = ⊥-elim ((lemma-free→¬# zfreeM) z#M)
  lemma w wfreeM
      | yes _ with z ≟ₐ z
  ... | yes _   = refl
  ... | no z≢z  = ⊥-elim (z≢z refl)
--
corollarylemma≺+ : {x y : Atom}{M : Λ} → y # ƛ x M → (M ∙ (ι ≺+ (x , v y))) ∙ (ι ≺+ (y , v x)) ≡ M ∙ (ι ≺+ (x , v x))
corollarylemma≺+ {x} {y} {M} y#ƛxM = sym (lemma≺+ y#ƛxM)
--
lemma≺+ι : {x y : Atom}{M : Λ} → y # ƛ x M → (M ∙ (ι ≺+ (x , v y))) ∙ (ι ≺+ (y , v x)) ≡ M ∙ ι
lemma≺+ι {x} {y} {M} y#ƛxM = begin≡
                               (M ∙ (ι ≺+ (x , v y))) ∙ (ι ≺+ (y , v x))
                             ≡⟨ corollarylemma≺+ y#ƛxM ⟩
                               M ∙ (ι ≺+ (x , v x))
                             ≡⟨ lemmaMι≺+x,x {x} {M} ⟩
                               M ∙ ι
                             ◻
\end{code}

\begin{code}
lemmaM∼M'→Mσ≡M'σ : {M M' : Λ}{σ : Σ}
  → M ∼α M' → M ∙ σ ≡ M' ∙ σ
lemmaM∼M'→Mσ≡M'σ ∼v              = refl
lemmaM∼M'→Mσ≡M'σ (∼· M∼M' N∼N') = cong₂ _·_ (lemmaM∼M'→Mσ≡M'σ M∼M') (lemmaM∼M'→Mσ≡M'σ N∼N')
lemmaM∼M'→Mσ≡M'σ {ƛ x M} {ƛ x' M'} {σ}
                 (∼ƛ .{M} .{M'} .{x} .{x'} {z} z#λxM z#λx'M' Mι≺+xz∼M'ι≺+x'z)
  with Chi' (σ , ƛ x M) | Chi' (σ , ƛ x' M')
    | χ-lemma3 σ σ (ƛ x M) (ƛ x' M')
         (λ _ _ → (λ _ yfreeσx → yfreeσx) , (λ _ yfreeσx → yfreeσx))
         ( (lemmaM∼M'→free→ {ƛ x M} {ƛ x' M'} (∼ƛ {M} {M'} {x} {x'} {z} z#λxM z#λx'M' Mι≺+xz∼M'ι≺+x'z)) ,
           (lemmaM∼M'→free← {ƛ x M} {ƛ x' M'} (∼ƛ {M} {M'} {x} {x'} {z} z#λxM z#λx'M' Mι≺+xz∼M'ι≺+x'z)))
... | y | .y | refl
  = cong (λ M → ƛ y M)
         (begin≡
           M ∙ (σ ≺+ (x , v y))
           ≡⟨ lemma≺+ z#λxM ⟩
           (M ∙ (ι ≺+ (x , v z))) ∙ (σ ≺+ (z , v y))
           ≡⟨ lemmaM∼M'→Mσ≡M'σ {M ∙ (ι ≺+ (x , v z))} {M' ∙ (ι ≺+ (x' , v z))} {σ ≺+ (z , v y)} Mι≺+xz∼M'ι≺+x'z ⟩
           (M' ∙ (ι ≺+ (x' , v z))) ∙ (σ ≺+ (z , v y))
           ≡⟨ sym (lemma≺+ z#λx'M') ⟩
           M' ∙ (σ ≺+ (x' , v y))
          ◻)
\end{code}

\begin{code}
open import Data.Nat.Induction

lemma-χι : (M : Λ) → Chi' (ι , M) # M
lemma-χι M = lemmafree#y→# (χ-lemma2 ι M)

lemmaMι≡M'ι→M∼M'-aux : (n : ℕ) →
  ((y : ℕ) → suc y ≤′ n → (M M' : Λ) → y ≡ length M → M ∙ ι ≡ M' ∙ ι → M ∼α M') →
  (M M' : Λ) → n ≡ length M → M ∙ ι ≡ M' ∙ ι → M ∼α M'
lemmaMι≡M'ι→M∼M'-aux .(suc zero) rec (v x)   (v .x)    refl refl = ∼v
lemmaMι≡M'ι→M∼M'-aux .(suc zero) rec (v x)   (M · N)   refl ()
lemmaMι≡M'ι→M∼M'-aux .(suc zero) rec (v x)   (ƛ y M)   refl ()
lemmaMι≡M'ι→M∼M'-aux n           rec (M · N) (v x)     _    ()
lemmaMι≡M'ι→M∼M'-aux .(length M + length N) rec (M · N) (M' · N') refl MNι≡M'N'ι
  = ∼·  (rec (length M) (lemmam>0→m+1≤m+n (length>0 {N})) M M' refl (proj₁ (lemmaMι≡M'ι MNι≡M'N'ι)))
        (rec (length N) (lemman>0→n+1≤m+n (length>0 {M})) N N' refl (proj₂ (lemmaMι≡M'ι MNι≡M'N'ι)) )
  where
  lemmaMι≡M'ι : (M · N) ∙ ι ≡ (M' · N') ∙ ι → M ∙ ι ≡ M' ∙ ι × N ∙ ι ≡ N' ∙ ι
  lemmaMι≡M'ι MNι≡M'N'ι with M' ∙ ι | N' ∙ ι | MNι≡M'N'ι
  ... | .(M ∙ ι) | .(N ∙ ι) | refl = refl , refl
lemmaMι≡M'ι→M∼M'-aux n           rec (M · N) (ƛ x M')  _    ()
lemmaMι≡M'ι→M∼M'-aux n           rec (ƛ x M) (v y)     _    ()
lemmaMι≡M'ι→M∼M'-aux n           rec (ƛ x M) (M' · N') _    ()
lemmaMι≡M'ι→M∼M'-aux .(suc (length M)) rec (ƛ x M) (ƛ x' M') refl λxMι≡λx'M'
  with lemmaλxMι≡λx'M'ι λxMι≡λx'M'
  where
  lemmaλxMι≡λx'M'ι : (ƛ x M) ∙ ι ≡ (ƛ x' M') ∙ ι →
                     Chi' (ι , ƛ x M) ≡ Chi' (ι , ƛ x' M') ×
                     M ∙ (ι ≺+ (x , v (Chi' (ι , ƛ x M)))) ≡ M' ∙ (ι ≺+ (x' , v (Chi' (ι , ƛ x' M'))))
  lemmaλxMι≡λx'M'ι λxMι#λx'M'ι with Chi' (ι , ƛ x M)    |   M ∙ (ι ≺+ (x , v (Chi' (ι , ƛ x M)))) | λxMι#λx'M'ι
  ... | .(Chi' (ι , ƛ x' M')) | .(M' ∙ (ι ≺+ (x' , v (Chi' (ι , ƛ x' M'))))) | refl = refl , refl
... | y≡y' , Mι≺+xy≡M'ι≺+xy'
  with Chi' (ι , ƛ x M) | Chi' (ι , ƛ x' M') | lemma-χι (ƛ x M) | lemma-χι (ƛ x' M') | y≡y'
... | y | .y | y#λxM | y#λx'M' | refl
  = ∼ƛ  {M} {M'} {x} {x'} {y} y#λxM y#λx'M'
        (rec (length (M ∙ (ι ≺+ (x , v y))))
             (lemmam≡n→m+1≤n+1 (lemma-length-corolary {x} {y} {M}))
             (M ∙ (ι ≺+ (x , v y)))
             (M' ∙ (ι ≺+ (x' , v y)))
             refl
             (cong (λ M → M ∙ ι) Mι≺+xy≡M'ι≺+xy'))

lemmaMι≡M'ι→M∼M' : {M M' : Λ} → M ∙ ι ≡ M' ∙ ι → M ∼α M'
lemmaMι≡M'ι→M∼M' {M} {M'} = (<′-rec _ lemmaMι≡M'ι→M∼M'-aux) (length M) M M' refl
\end{code}

\begin{code}
∼ρ : Reflexive _∼α_
∼ρ {M} = lemmaMι≡M'ι→M∼M' refl

id-ren-α : ∀ M σ ρ → Σ∼Ren σ ρ M → M ∙ᵣ ρ ∼α M ∙ σ
id-ren-α M σ ρ cond rewrite id-ren {M} cond = ∼ρ

\end{code}
\begin{code}
∼σ : Symmetric _∼α_
∼σ {M} {N} M∼N
  = lemmaMι≡M'ι→M∼M'
          (sym (lemmaM∼M'→Mσ≡M'σ M∼N))
\end{code}
\begin{code}
∼τ : Transitive _∼α_
∼τ {M} {N} {P} M∼N N∼P
  = lemmaMι≡M'ι→M∼M'
         (trans (lemmaM∼M'→Mσ≡M'σ M∼N)
                (lemmaM∼M'→Mσ≡M'σ N∼P))
\end{code}

\begin{code}
≈-preorder∼ : Preorder _ _ _
≈-preorder∼ =
    record {
      Carrier = Λ;
      _≈_ = _≡_;
      _∼_ = _∼α_;
      isPreorder =  record {
        isEquivalence = Relation.Binary.Setoid.isEquivalence (setoid Λ) ;
        reflexive = λ { {M} {.M} refl → ∼ρ};
        trans = ∼τ } }

import Relation.Binary.Reasoning.Preorder as PreR
open PreR ≈-preorder∼ hiding (step-≡) public

lemma-σ⇂ : {M : Λ}{σ σ' : Σ} → σ ∼α σ' ⇂ M → ((ι ∘ σ) , M) ≅⇂ ((ι ∘ σ') , M)
lemma-σ⇂ σ∼σ'⇂M  = ∼*ρ , (λ x xfreeM → lemmaM∼M'→Mσ≡M'σ (σ∼σ'⇂M  x xfreeM))
--
lemma-subst-σ∼ : {M : Λ}{σ σ' : Σ} → σ ∼α σ' ⇂ M → M ∙ σ ∼α M ∙ σ'
lemma-subst-σ∼ {M} {σ} {σ'} σ∼ασ'⇂M
  = lemmaMι≡M'ι→M∼M' (begin≡
                        (M ∙ σ) ∙ ι
                        ≡⟨ lemma· {M} {σ} {ι} ⟩
                        M ∙ (ι ∘ σ)
                        ≡⟨  lemma-subst-σ≡ {M} {ι ∘ σ} {ι ∘ σ'} (lemma-σ⇂ σ∼ασ'⇂M) ⟩
                        M ∙ (ι ∘ σ')
                        ≡⟨ sym (lemma· {M} {σ'} {ι}) ⟩
                        (M ∙ σ') ∙ ι
                      ◻)
\end{code}

\begin{code}
lemma-subst : {M M' : Λ}{σ σ' : Σ} →
  M ∼α M' → σ ∼α σ' ⇂ M → (M ∙ σ) ∼α (M' ∙ σ')
lemma-subst {M} {M'} {σ} {σ'} M∼M' σ∼σ'⇂M
  =  begin
       M ∙ σ
       ∼⟨ lemma-subst-σ∼ σ∼σ'⇂M ⟩
       M ∙ σ'
       ≈⟨ lemmaM∼M'→Mσ≡M'σ M∼M'  ⟩
       M' ∙ σ'
     ∎
\end{code}



\begin{code}
lemma∙ι : {M : Λ} → M ∼α M ∙ ι
lemma∙ι {M} =  lemmaMι≡M'ι→M∼M' ( begin≡
                                    M ∙ ι
                                  ≡⟨ lemma1 {M} {ι} {ι ∘ ι} (∼*ρ , (λ _ _ → refl) ) ⟩
                                    M ∙ (ι ∘ ι)
                                  ≡⟨  sym (lemma· {M} {ι} {ι}) ⟩
                                    (M ∙ ι) ∙ ι
                                  ◻)

lemma∙ιᵣ : {M : Λ} → M ∼α M ∙ᵣ ιᵣ
lemma∙ιᵣ {M} rewrite id-eq M = lemma∙ι {M}

lemma∙ιᵣ' : {M : Λ} → M ∼αᵣ M ∙ᵣ ιᵣ
lemma∙ιᵣ' {M} = α→αᵣ (lemma∙ιᵣ {M})


lemma∙compᵣ : {M : Λ} {r r' : Ren} → (M ∙ᵣ r) ∙ᵣ r' ≡ M ∙ᵣ (r' ∘f r)
lemma∙compᵣ {M} {r} {r'} = goal
  where a : (M ∙ᵣ r) ∙ᵣ r' ≡ (M ∙ (v ∘f r)) ∙ (v ∘f r')
        a = trans (cong (_∙ᵣ r') (id-ren' M r)) (id-ren' (M ∙ (v ∘f r)) r')
        b : M ∙ᵣ (r' ∘f r) ≡ M ∙ (v ∘f (r' ∘f r))
        b = id-ren' M (r' ∘f r)
        goal : ((M ∙ᵣ r) ∙ᵣ r') ≡ (M ∙ᵣ (r' ∘f r))
        goal rewrite a | b  = lemma· {M} {v ∘f r} {v ∘f r'}
\end{code}

\begin{code}
lemma∼λ : {M N : Λ}{x : Atom} → M ∼α N → ƛ x M ∼α ƛ x N
lemma∼λ {M} {N} {x} M∼N = ∼ƛ #ƛ≡ #ƛ≡ lemma∼ƛaux
  where
  lemma∼ƛaux : M ∙ (ι ≺+ (x , v x)) ∼α N ∙ (ι ≺+ (x , v x))
  lemma∼ƛaux rewrite lemmaM∼M'→Mσ≡M'σ {σ = ι ≺+ (x , v x)} M∼N = ∼ρ
\end{code}


\begin{code}
infix 1 _∼ασ_
_∼ασ_ : Σ → Σ → Set
σ ∼ασ σ' = (x : Atom) → σ x ∼α σ' x

lemma∼ασ : {σ σ' : Σ}{M : Λ} → σ ∼ασ σ' → σ ∼α σ' ⇂ M
lemma∼ασ σ∼ασ' x x*M = σ∼ασ' x

lemmaι∘σ : {σ : Σ} → ι ∘ σ ∼ασ σ
lemmaι∘σ {σ} x = begin
                   σ x ∙ ι
                 ∼⟨ ∼σ (lemma∙ι) ⟩
                   σ x
                 ∎

lemma∼≺+ : {x : Atom}{N : Λ}{σ σ' : Σ} → σ ∼ασ σ' → σ ≺+ (x , N) ∼ασ σ' ≺+ (x , N)
lemma∼≺+ {x} σ∼σ' y with x ≟ₐ y
... | yes  _ = ∼ρ
... | no   _ = σ∼σ' y

prop8 : {x y : Atom}{σ : Σ}{M N : Λ} → y #⇂ (σ , ƛ x M) → (ι ≺+ (y , N) ∘ σ ≺+ (x , v y)) ∼α σ ≺+ (x , N) ⇂ M
prop8 {x} {y} {σ} {M} {N} y#⇂ƛxM z z*M =
                begin
                  (ι ≺+ (y , N) ∘ σ ≺+ (x , v y)) z
                ≈⟨ lemmaσ∘≺+ M N σ ι x y y#⇂ƛxM z z*M ⟩
                  ((ι ∘ σ) ≺+ (x , N)) z
                ∼⟨ (lemma∼≺+ {x} {N} (lemmaι∘σ {σ})) z ⟩
                  (σ ≺+ (x , N)) z
                ∎

corollary1Prop7 : {M N : Λ}{σ : Σ}{x : Atom} → M ∙ (σ ≺+ (x , N ∙ σ)) ≡ (M ∙ (ι ≺+ (x , N))) ∙ σ
corollary1Prop7 {M} {N} {σ} {x}
  = begin≡
      M ∙ (σ ≺+ (x , N ∙ σ))
   ≡⟨ lemma1 {M} (prop6 (lemma≅≺+ {x} {N ∙ σ} (lemmaι {σ}))) ⟩
      M ∙ ((σ ∘ ι) ≺+ (x , N ∙ σ))
   ≡⟨ lemma1  (prop6 {(σ ∘ ι) ≺+ (x , N ∙ σ)} {σ ∘ ι ≺+ (x , N)} {M} (prop7 {x})) ⟩
      M ∙ (σ ∘ ι ≺+ (x , N))
   ≡⟨  sym (lemma· {M}) ⟩
      (M ∙ (ι ≺+ (x , N))) ∙ σ
    ◻

corollary1SubstLemma : {x y : Atom} {σ : Σ}{M N : Λ} → y #⇂ (σ , ƛ x M) → (M ∙ (σ ≺+ (x , v y))) ∙ (ι ≺+ (y , N)) ∼α M ∙ (σ ≺+ (x , N))
corollary1SubstLemma {x} {y} {σ} {M} {N} y#⇂σ,ƛxM
  =  begin
       (M ∙ (σ ≺+ (x , v y))) ∙ (ι ≺+ (y , N))
     ≈⟨ lemma· {M} ⟩
       M ∙ (ι ≺+ (y , N) ∘ σ ≺+ (x , v y))
     ∼⟨ lemma-subst-σ∼ (prop8 y#⇂σ,ƛxM) ⟩
       M ∙ (σ ≺+ (x , N))
     ∎
 \end{code}


Corollary 4-2

\begin{code}

∉-++⁻ˡ : {A : Set} {x : A}{xs ys : List A} → x ∉ xs ++ ys → x ∉ xs
∉-++⁻ˡ c∉xs++ys c∈xs = c∉xs++ys (∈-++⁺ˡ c∈xs)
∉-++⁻ʳ : {A : Set} {y : A}{xs ys : List A} → y ∉ xs ++ ys → y ∉ ys
∉-++⁻ʳ {xs = xs} {ys} c∉xs++ys c∈ys = c∉xs++ys (∈-++⁺ʳ xs c∈ys)

corollary4-2  : {x y : Atom}{M : Λ}{σ : Σ}
              → y #⇂ (σ , ƛ x M)
              → ƛ x M ∙ σ ∼α ƛ y (M ∙ (σ ≺+ (x , v y)))
corollary4-2 {x} {y} {M} {σ} y#⇂σ,ƛxM
  = begin
      ƛ x M ∙ σ
    ≈⟨ refl ⟩
      ƛ z (M ∙ (σ ≺+ (x , v z)))
    ∼⟨ ∼ƛ  {y = w} w#ƛzM∙σ≺+x,z w#ƛyM∙σ≺+x,y
           (begin
             (M ∙ (σ ≺+ (x , v z))) ∙ (ι ≺+ (z , v w))
           ∼⟨ corollary1SubstLemma z#⇂σ,ƛxM  ⟩
             M ∙ (σ ≺+ (x , v w))
           ∼⟨ ∼σ (corollary1SubstLemma y#⇂σ,ƛxM) ⟩
             (M ∙ (σ ≺+ (x , v y))) ∙ (ι ≺+ (y , v w))
           ∎)         ⟩
      ƛ y (M ∙ (σ ≺+ (x , v y)))
    ∎
  where
  z = Chi' (σ , ƛ x M)
  z#⇂σ,ƛxM : z #⇂ (σ , ƛ x M)
  z#⇂σ,ƛxM = χ-lemma2 σ (ƛ x M)
  w : Atom
  w =  χ' ((fv (ƛ z (M ∙ (σ ≺+ (x , v z))))) ++ fv (ƛ y (M ∙ (σ ≺+ (x , v y)))))
  w#ƛzM∙σ≺+x,z : w # ƛ z (M ∙ (σ ≺+ (x , v z)))
  w#ƛzM∙σ≺+x,z = lemma∉fv→# (∉-++⁻ˡ  (lemmaχ∉ (fv (ƛ z (M ∙ (σ ≺+ (x , v z)))) ++ fv (ƛ y (M ∙ (σ ≺+ (x , v y)))))))
  w#ƛyM∙σ≺+x,y : w # ƛ y (M ∙ (σ ≺+ (x , v y)))
  w#ƛyM∙σ≺+x,y = lemma∉fv→# (∉-++⁻ʳ  {xs = fv (ƛ z (M ∙ (σ ≺+ (x , v z))))}
                                             (lemmaχ∉ (fv (ƛ z (M ∙ (σ ≺+ (x , v z)))) ++ fv (ƛ y (M ∙ (σ ≺+ (x , v y)))))))
\end{code}


\begin{code}
corollary4-2' : {x y : Atom}{M : Λ}
              → y # ƛ x M
              → ƛ x M ∼α ƛ y (M ∙ (ι ≺+ (x , v y)))
corollary4-2' {x} {y} {M} y#ƛxM
  =  begin
        ƛ x M
      ∼⟨ lemma∙ι ⟩
        ƛ x M ∙ ι
      ∼⟨ corollary4-2 (lemma#→ι#⇂ y#ƛxM)  ⟩
        ƛ y (M ∙ (ι ≺+ (x , v y)))
      ∎
\end{code}

\begin{code}
lemmaƛ∼[] : {x : Atom}{M : Λ}{σ : Σ} → x #⇂ (σ , M) → σ x ≡ v x
  → ƛ x M ∙ σ ∼α  ƛ x (M ∙ σ)
lemmaƛ∼[] {x} {M} {σ} x#⇂σ,M σx≡x
  =  begin
       ƛ x M ∙ σ
     ∼⟨ corollary4-2 {x} {x} {M} {σ} (λ { y (*ƛ y*M _) → x#⇂σ,M y y*M }) ⟩
       ƛ x (M ∙ (σ ≺+ (x , v x)))
     ∼⟨ ∼ƛ {y = y} y#ƛxM∙σ≺+x,x y#ƛyM∙σ
                   (begin
                     (M ∙ (σ ≺+ (x , v x))) ∙ (ι ≺+ (x , v y))
                   ≈⟨ lemmaM∼M'→Mσ≡M'σ  {M ∙ (σ ≺+ (x , v x))} {M ∙ σ} {ι ≺+ (x , v y)}
                                        (begin
                                          M ∙ (σ ≺+ (x , v x))
                                        ≈⟨ lemmaσ≡σ'→Mσ≡Mσ' {M} (∼*ρ , lemma) ⟩
                                          M ∙ σ
                                        ∎) ⟩
                      (M ∙ σ) ∙ (ι ≺+ (x , v y))
                   ∎) ⟩
       ƛ x (M ∙ σ)
     ∎
  where
  y = χ' (fv (ƛ x (M ∙ (σ ≺+ (x , v x)))) ++ fv (ƛ x (M ∙ σ)))
  y#ƛxM∙σ≺+x,x : y # ƛ x (M ∙ (σ ≺+ (x , v x)))
  y#ƛxM∙σ≺+x,x = lemma∉fv→# (∉-++⁻ˡ  {xs = fv (ƛ x (M ∙ (σ ≺+ (x , v x))))}
                                            (lemmaχ∉ (fv (ƛ x (M ∙ (σ ≺+ (x , v x)))) ++ fv (ƛ x (M ∙ σ)))))
  y#ƛyM∙σ : y # ƛ x (M ∙ σ)
  y#ƛyM∙σ = lemma∉fv→# (∉-++⁻ʳ {xs = fv (ƛ x (M ∙ (σ ≺+ (x , v x))))}
                                       (lemmaχ∉ (fv (ƛ x (M ∙ (σ ≺+ (x , v x)))) ++ fv (ƛ x (M ∙ σ)))))
  lemma : (z : Atom) → z * M → (σ ≺+ (x , v x)) z ≡ σ z
  lemma z z*M with x ≟ₐ z
  ... | no _      = refl
  lemma .x x*M
      | yes refl  = sym σx≡x
\end{code}
%</naivesubstitution>
