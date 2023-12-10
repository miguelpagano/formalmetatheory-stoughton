\begin{code}
open import Relation.Binary.Definitions
open import Relation.Binary.PropositionalEquality hiding ([_])

import Atom
module Substitution {Atom : Set} (_≟ₐ_ : Decidable {A = Atom} _≡_) (Χ : Atom.Chi _≟ₐ_) where
open Atom _≟ₐ_
open import Term _≟ₐ_ Χ hiding (_×_;∃)

open import Function renaming (_∘_ to _∘f_)
open import Function.Inverse hiding (sym;_∘_;map;id;Inverse)
open Inverse
import Function.Equality as FE
open import Data.List hiding (any) renaming (length to length')
open import Data.List.Relation.Unary.Any as Any hiding (map)
open import Data.List.Relation.Binary.Subset.Propositional
open import Data.List.Membership.Propositional
open import Data.List.Relation.Unary.Any hiding (map)
open import Data.List.Relation.Unary.Any.Properties
open import Data.List.Membership.Propositional.Properties
open import Data.Bool hiding (_≟_;_∨_)
open import Data.Sum hiding (map) renaming (_⊎_ to _∨_)
open import Data.Empty
open import Data.Nat hiding (_*_)
open import Data.Product renaming (Σ to Σₓ;map to mapₓ)
open import Relation.Binary
open import Relation.Binary.PropositionalEquality as PropEq renaming ([_] to [_]ᵢ)
open import Relation.Nullary
open import Relation.Nullary.Negation
open import Relation.Nullary.Decidable hiding (map)
open import Algebra.Structures

-- open ≤-Reasoning
--    renaming (begin_ to start_; _∎ to _◽; _≡⟨_⟩_ to _≤⟨_⟩'_)

infixl 8 _≺+_
\end{code}

Substitutions are functions from variables to terms and renamings are functions from variables to variables.

\begin{code}
Σ = Atom → Λ
Ren = Atom → Atom
\end{code}

\begin{code}
ι : Σ
ι = id ∘f v
ιᵣ : Ren
ιᵣ = id
\end{code}

Update of functions at a point.
\begin{code}
_≺+_ : {A : Set} → (Atom → A) → (Atom × A) → (Atom → A)
(σ ≺+ (x , M)) y with x ≟ₐ y
... | yes _ = M
... | no  _ = σ y
\end{code}

\begin{code}
x≢y→x[y/M]≡x : {A : Set} {x y : Atom} {M : A} {f : Atom → A} → x ≢ y → (f ≺+ (x , M)) y ≡ f y
x≢y→x[y/M]≡x {x = x} {y} x≢y with x ≟ₐ y
... | yes x≡y = ⊥-elim (x≢y x≡y)
... | no  _   = refl

x≡y→x[y/M]≡x : {A : Set} {x y : Atom} {M : A} {f : Atom → A} → x ≡ y → (f ≺+ (x , M)) y ≡ M
x≡y→x[y/M]≡x {x = x} {y} x≡y with x ≟ₐ y
... | yes x≡y = refl
... | no  neq   = ⊥-elim (neq x≡y)

\end{code}

\begin{code}
ι-≡ : ∀ x → ι x ≡ (v Function.∘ ιᵣ) x
ι-≡ x = refl
\end{code}
-- %<*sigmatype>

Restriction of a substitution to a term.

\begin{code}
R = Σ × Λ
Rᵣ = Ren × Λ
\end{code}

Freshness in a restriction is defined as follows:

\begin{code}
_#⇂_ : Atom → R → Set
x #⇂ (σ , M) = (y : Atom) → y * M → x # (σ y)
\end{code}


\begin{code}
lemma#→ι#⇂ : {x y : Atom}{M : Λ} → x # ƛ y M → x #⇂ (ι , ƛ y M)
lemma#→ι#⇂ {x} {y} {M} x#ƛyM z z*ƛyM with z ≟ₐ x
... | no  z≢x  = #v z≢x
lemma#→ι#⇂ {x} {y} {M} x#ƛyM .x x*ƛyM
    | yes refl = ⊥-elim (lemma#→¬free x#ƛyM x*ƛyM)
\end{code}

-- Free

\begin{code}
_*⇂_ : Atom → R → Set
x *⇂ (σ , M) = ∃ (λ y  → (y * M) × (x * σ y))
\end{code}

The right notion of identity of substitutions has to be formulated for restrictions:

\begin{code}
infix 1 _≅σ_
_≅σ_ : Σ → Σ → Set
σ ≅σ σ' = (x : Atom) → σ x ≡ σ' x

lemmaσ≺+x,x≅σ : {x : Atom} → ι ≺+ (x , v x) ≅σ ι
lemmaσ≺+x,x≅σ {x} y with x ≟ₐ y
... | no   _     = refl
lemmaσ≺+x,x≅σ {x} .x
    | yes  refl  = refl

_≅⇂_ : R → R → Set
(σ , M) ≅⇂ (σ' , M') = (M ∼* M') × ((x : Atom) → x * M → σ x ≡ σ' x)

_≅_⇂_ : Σ → Σ → Λ → Set
σ ≅ σ' ⇂ M = (σ , M) ≅⇂ (σ' , M)

lemma≅≺+ : {x : Atom}{N : Λ}{σ σ' : Σ} → σ ≅σ σ' → σ ≺+ (x , N) ≅σ σ' ≺+ (x , N)
lemma≅≺+ {x} σ≌σ' y with x ≟ₐ y
... | yes  _ = refl
... | no   _ = σ≌σ' y

prop6 : {σ σ' : Σ}{M : Λ} → σ ≅σ σ' → σ ≅ σ' ⇂ M
prop6 σ≅σ' = ((λ _ → id) , (λ _ → id)) , λ x _ → σ≅σ' x
\end{code}

\begin{code}
_∼*⇂_ : R → R → Set
(σ , M) ∼*⇂ (σ' , M') =  ((x : Atom) → x *⇂ (σ , M) → x *⇂ (σ' , M')) ×
                         ((x : Atom) → x *⇂ (σ' , M') → x *⇂ (σ , M))
\end{code}

\begin{code}
fv : Λ → List Atom
fv (v a)     = [ a ]
fv (M · N)   = fv M ++ fv N
fv (ƛ a M)   = fv M -ₐ a
--
lemmafvfree→ : (x : Atom)(M : Λ) → x ∈ fv M → x * M
lemmafvfree→ x (v y)    (here x≡y) with y ≟ₐ x
... | no   y≢x = ⊥-elim (y≢x (sym x≡y))
lemmafvfree→ x (v .x)    (here x≡x)
    | yes  refl = *v
lemmafvfree→ x (v y) (there ())
lemmafvfree→ x (M · N)  x∈fvMN with ∈-++⁻ (fv M) x∈fvMN
... | inj₁ x∈fvM = *·l (lemmafvfree→ x M x∈fvM)
... | inj₂ x∈fvN = *·r (lemmafvfree→ x N x∈fvN)
lemmafvfree→ x (ƛ y M)  x∈fvM-y with y ≟ₐ x | ∈-filter⁻ (λ z → ¬? (y ≟ₐ z)) x∈fvM-y
... | no y≢x   | x∈fvM , _ = *ƛ (lemmafvfree→ x M x∈fvM) y≢x -- *ƛ (lemmafvfree→ x M x∈fvM) y≢x
lemmafvfree→ x (ƛ .x M)  x∈fvM-y
     | yes refl | x∈fvM , neq = ⊥-elim (neq refl)
--
lemmafvfree← : (x : Atom)(M : Λ) → x * M → x ∈ fv M
lemmafvfree← x (v .x)    *v
  = here refl
lemmafvfree← x .(M · N)  (*·l {.x} {M} {N} xfreeM)
  = ∈-++⁺ˡ (lemmafvfree← x M xfreeM)
lemmafvfree← x .(M · N)  (*·r {.x} {M} {N} xfreeN)
  = ∈-++⁺ʳ (fv M) (lemmafvfree← x N xfreeN)
lemmafvfree← x .(ƛ y M)  (*ƛ {.x} {y} {M} xfreeM y≢x)
  = ∈-filter⁺ (λ z → ¬? (y ≟ₐ z)) ((lemmafvfree← x M xfreeM)) y≢x
  where
  px≡true : not ⌊ y ≟ₐ x ⌋ ≡ true
  px≡true with y ≟ₐ x
  ... | yes y≡x = ⊥-elim (y≢x y≡x)
  ... | no  _   = refl

fv-app⁺ˡ : ∀ {M N x} → x ∈ fv M → x ∈ fv (M · N)
fv-app⁺ˡ x∈M = ∈-++⁺ˡ x∈M
fv-app⁺ʳ : ∀ {M N x} → x ∈ fv N → x ∈ fv (M · N)
fv-app⁺ʳ {M} x∈N = ∈-++⁺ʳ (fv M) x∈N

fv-abs⁻ : ∀ {M x y} → x ∈ fv (ƛ y M) → (x ∈ fv M) × (x ≢ y)
fv-abs⁻ {M} {x} {y}  xfv with *-abs⁻ {x} {y} {M} (lemmafvfree→ x (ƛ y M) xfv)
... | xfvM , x≢y = (lemmafvfree← _ _ xfvM) , x≢y
\end{code}

\begin{code}
lemma∉fv→# : ∀ {a : Atom}{M : Λ} → a ∉ fv M → a # M
lemma∉fv→# {a} {M} a∉fvM with a #? M
... | yes a#M = a#M
... | no ¬a#M = ⊥-elim (a∉fvM (lemmafvfree← a M (lemma¬#→free ¬a#M)))
\end{code}

-- Chi encapsulation

\begin{code}
open Atom.Chi Χ
Chi' : R → Atom
Chi' (σ , M) = χ' (concat (Data.List.map (fv ∘f σ) (fv M)))

Chiᵣ : Rᵣ → Atom
Chiᵣ (ren , M) = χ' (Data.List.map ren (fv M))

Chiᵣ-eq : ∀ M ren → Chiᵣ (ren , M) ≡ Chi' (v ∘f ren , M)
Chiᵣ-eq M ren = cong χ' (equiv (fv M))
  where equiv : ∀ xs → map ren xs ≡ concat (map (λ x → [ ren x ]) xs)
        equiv [] = refl
        equiv (x ∷ xs) = cong (ren x ∷_) (equiv xs)
\end{code}

\begin{code}
χₜ : Λ → Atom
χₜ M = χ' (fv M)
--
lemmaχₜ# : {M : Λ} → χₜ M # M
lemmaχₜ# {M} = lemma∉fv→# (lemmaχ∉ (fv M))
\end{code}

\begin{code}
open Function.Inverse.Inverse
χ-lemma2 : (σ : Σ)(M : Λ) → Chi' (σ , M) #⇂ (σ , M)
χ-lemma2 σ M y yfreeM with Chi' (σ , M) #? σ y
... | yes χσM#σy = χσM#σy
... | no ¬χσM#σy = ⊥-elim (χ∉concatmapfv∘σfvM χ∈concatmapfv∘σfvM)
  where
  -- Using lemma lemmaχ∉ we know χ' not in the list (concat (map (fv ∘ σ) (fv M))) passed
  χ∉concatmapfv∘σfvM : Chi' (σ , M) ∉ (concat (map (fv ∘f σ) (fv M)))
  χ∉concatmapfv∘σfvM = lemmaχ∉ (concat (map (fv ∘f σ) (fv M)))
  -- y * M ⇒ y ∈ fv M
  y∈fvM : y ∈ fv M
  y∈fvM = lemmafvfree← y M yfreeM
  -- due to y ∈ fv M we have that fv (σ y) ∈ map (fv ∘ σ) (fv M)
  fvσy∈mapfv∘σfvM : fv (σ y) ∈ (map (fv ∘f σ) (fv M))
  fvσy∈mapfv∘σfvM = ((FE.Π._⟨$⟩_ (to (map-∈↔ (fv ∘f σ) {y = fv (σ y)} {xs = fv M}))) (y , y∈fvM , refl))
  -- we know ¬ χ' # σ y ⇒ χ' * (σ y), and then χ' ∈ fv (σ y)
  χfreeσy : Chi' (σ , M) ∈ (fv (σ y))
  χfreeσy = lemmafvfree← (Chi' (σ , M)) (σ y) (lemma¬#→free ¬χσM#σy)
  -- χ' ∈ fv (σ y) and fv (σ y) ∈ map (fv ∘ σ) (fv M) ⇒ χ' ∈ concat (map (fv ∘f σ) (fv M))
  χ∈concatmapfv∘σfvM : Chi' (σ , M) ∈ (concat (map (fv ∘f σ) (fv M)))
  χ∈concatmapfv∘σfvM = (FE.Π._⟨$⟩_ (to (concat-∈↔ {xss = map (fv ∘f σ) (fv M)}))) (fv (σ y) ,  χfreeσy , fvσy∈mapfv∘σfvM)
--
χ-lemma4 :  (σ σ' : Σ)(M M' : Λ) → (σ , M) ∼*⇂ (σ' , M') →
            Chi' (σ , M) ≡ Chi' (σ' , M')
χ-lemma4 σ σ' M M' (h1 , h2)
  = lemmaχaux⊆ ((concat (map (fv ∘f σ) (fv M)))) (concat (map (fv ∘f σ') (fv M'))) lemma⊆ lemma⊇
  where
  lemma⊆ : ((concat (map (fv ∘f σ) (fv M)))) ⊆ (concat (map (fv ∘f σ') (fv M')))
  lemma⊆ {y} y∈concat
    with (FE.Π._⟨$⟩_ (from (concat-∈↔ {xss = map (fv ∘f σ) (fv M)}))) y∈concat
  ... | xs , y∈xs , xs∈map
    with (FE.Π._⟨$⟩_ (from ((map-∈↔ (fv ∘f σ) {xs = fv M})))) xs∈map
  lemma⊆ {y} y∈concat
      | .(fv (σ x)) , y∈fvσx , fvσx∈map
      | x , x∈fvM , refl
    with lemmafvfree→ x M x∈fvM | lemmafvfree→ y (σ x) y∈fvσx
  ... | xfreeM | yfreeσx
    with h1 y (x , xfreeM , yfreeσx)
  ... | u , ufreeM' , yfreeσ'u
    with lemmafvfree← u M' ufreeM' | lemmafvfree← y (σ' u) yfreeσ'u
  ... | u∈fvM' | y∈fvσ'u
    with (FE.Π._⟨$⟩_ (to ((map-∈↔ (fv ∘f σ') {y = fv (σ' u)} {xs = fv M'})))) (u , u∈fvM' , refl)
  ... | fvσ'u∈map
     = (FE.Π._⟨$⟩_ (to (concat-∈↔ {xss = map (fv ∘f σ') (fv M')}))) (fv (σ' u) , y∈fvσ'u , fvσ'u∈map)
  lemma⊇ : (concat (map (fv ∘f σ') (fv M'))) ⊆ ((concat (map (fv ∘f σ) (fv M))))
  lemma⊇ {y} y∈concat
    with (FE.Π._⟨$⟩_ (from (concat-∈↔  {xss = map (fv ∘f σ') (fv M')}))) y∈concat
  ... | xs , y∈xs , xs∈map
    with (FE.Π._⟨$⟩_ (from ((map-∈↔ ((fv ∘f σ')) {xs = fv M'})))) xs∈map
  lemma⊇ {y} y∈concat
      | .(fv (σ' x)) , y∈fvσ'x , fvσ'x∈map
      | x , x∈fvM' , refl
    with lemmafvfree→ x M' x∈fvM' | lemmafvfree→ y (σ' x) y∈fvσ'x
  ... | xfreeM' | yfreeσ'x
    with h2 y (x , xfreeM' , yfreeσ'x)
  ... | u , ufreeM , yfreeσu
    with lemmafvfree← u M ufreeM | lemmafvfree← y (σ u) yfreeσu
  ... | u∈fvM | y∈fvσu
    with (FE.Π._⟨$⟩_ (to ((map-∈↔ (fv ∘f σ) {y = fv (σ u)} {xs = fv M})))) (u , u∈fvM , refl)
  ... | fvσu∈map
     = (FE.Π._⟨$⟩_ (to (concat-∈↔ {xss = map (fv ∘f σ) (fv M)}))) (fv (σ u) , y∈fvσu , fvσu∈map)
--
χ-lemma3 : (σ σ' : Σ)(M M' : Λ) →
   (∀ x → x * M → σ x ∼* σ' x)   →
   M ∼* M' →
   Chi' (σ , M) ≡ Chi'  (σ' , M')
χ-lemma3 σ σ' M M' x*M⇛σx∼σ'x (*M⇒M' , *M'⇒M) = χ-lemma4 σ σ' M M' (h1 , h2)
  where
  h1 : (y : Atom) → ∃ (λ x → (x * M)  × (y * σ x))  → ∃ (λ u → (u * M') ×  (y * σ' u))
  h1 y (x , x*M , y*σx)    =  x , *M⇒M' x x*M , proj₁ (x*M⇛σx∼σ'x x x*M) y y*σx
  h2 : (y : Atom) → ∃ (λ x → (x * M') × (y * σ' x)) → ∃ (λ u → (u * M) ×  (y * σ u))
  h2 y (x , x*M' , y*σ'x)  =  x , *M'⇒M x x*M' , proj₂ (x*M⇛σx∼σ'x x (*M'⇒M x x*M')) y y*σ'x
\end{code}

\begin{code}
_∙_ : Λ → Σ → Λ
(v x)    ∙ σ = σ x
(M · N)  ∙ σ = (M ∙ σ) · (N ∙ σ)
(ƛ x M)  ∙ σ = ƛ y (M ∙ (σ ≺+ (x , v y)))
  where y = Chi' (σ , ƛ x M)

_∙ᵣ_ : Λ → Ren → Λ
(v x)    ∙ᵣ σ = v (σ x)
(M · N)  ∙ᵣ σ = (M ∙ᵣ σ) · (N ∙ᵣ σ)
(ƛ x M)  ∙ᵣ σ = ƛ y (M ∙ᵣ (σ ≺+ (x , y)))
  where y = Chiᵣ (σ , ƛ x M)

∼*eq :  ∀ M (σ : Σ) (ρ : Ren) → (∀ x → x ∈ fv M → v (ρ x) ≡ σ x) → (x₁ : Atom) → x₁ * M → v (ρ x₁) ∼* σ x₁
∼*eq M σ ρ cond x xfv rewrite cond x (lemmafvfree← x M xfv) = ∼*ρ

Σ∼Ren : Σ → Ren → Λ → Set
Σ∼Ren σ ρ M = ∀ x → x ∈ fv M → v (ρ x) ≡ σ x

ι∼Renιᵣ : ∀ M → Σ∼Ren ι ιᵣ M
ι∼Renιᵣ M = (λ _ _ → refl)

Σ∼Ren-upd : ∀ σ ρ M → Σ∼Ren σ ρ M → ∀ x y → Σ∼Ren (σ ≺+ (x , v y)) (ρ ≺+ (x ∶ y)) M
Σ∼Ren-upd σ ρ M cond x y z z∈fvM with x ≟ₐ z
... | yes eq rewrite x≡y→x[y/M]≡x {x = x} {y = z} {M = v y} {f = σ} eq = refl
... | no neq rewrite x≢y→x[y/M]≡x {x = x} {y = z} {M = v y} {f = σ} neq |
                     x≢y→x[y/M]≡x {x = x} {y = z} {M = y} {f = ρ} neq = cond z z∈fvM

id-ren : ∀ M σ ρ → Σ∼Ren σ ρ M → M ∙ᵣ ρ ≡ M ∙ σ
id-ren (v x) σ ρ eq = eq x (here refl)
id-ren (M · N) σ ρ eq = PropEq.cong₂ _·_ (id-ren M σ ρ λ x x∈M → eq x (fv-app⁺ˡ {M = M} {N = N} x∈M)) (id-ren N σ ρ λ x x∈N → eq x (fv-app⁺ʳ {M = M} {N = N} x∈N))
id-ren (ƛ x M) σ ρ eq = PropEq.cong₂ ƛ (sym y=y) (id-ren M (σ ≺+ (x , v y)) (ρ ≺+ (x , y')) p)
  where y = Chi' (σ , ƛ x M)
        y' = Chiᵣ (ρ , ƛ x M)
        y=y : y ≡ Chiᵣ (ρ , ƛ x M)
        y=y rewrite Chiᵣ-eq (ƛ x M) ρ = sym (χ-lemma3 (v ∘f ρ) σ (ƛ x M) (ƛ x M) (∼*eq (ƛ x M) σ ρ eq) ∼*ρ)
        p : (x₁ : Atom) → x₁ ∈ fv M → v ((ρ ≺+ (x ∶ y')) x₁) ≡ (σ ≺+ (x ∶ v y)) x₁
        p z z∈fvM with x ≟ₐ z
        ... | yes eq = cong v (sym y=y)
        ... | no neq = eq z (∈-filter⁺ (λ a → ¬? (x ≟ₐ a)) z∈fvM neq)

id-ren' : ∀ M ρ → M ∙ᵣ ρ ≡ M ∙ (v ∘f ρ)
id-ren' M ρ = id-ren M (v ∘f ρ) ρ (λ _ _ → refl)

id-eq : ∀ M →  M ∙ᵣ ιᵣ ≡ M ∙ ι
id-eq M = id-ren M ι ιᵣ (ι∼Renιᵣ M)
\end{code}

-- \begin{code}
infixl  7 _∘_
_∘_ : Σ → Σ → Σ
(σ ∘ σ') x = (σ' x) ∙ σ

lemmaι : {σ : Σ} → σ ≅σ σ ∘ ι
lemmaι x = refl
\end{code}

\begin{code}
prop7 : {x : Atom}{σ σ' : Σ}{M : Λ} → (σ' ∘ σ) ≺+ (x , M ∙ σ') ≅σ σ' ∘ (σ ≺+ (x , M))
prop7 {x} {σ} {σ'} {M} y with x ≟ₐ y
... | yes _  = refl
... | no _   = refl
\end{code}

\begin{code}
x≢y→x*x[y/M] : {x y : Atom}{M : Λ} → x ≢ y → y * (v y ∙ (ι ≺+ (x , M)))
x≢y→x*x[y/M] {x} {y} {M} x≢y with (ι ≺+ (x , M)) y | x≢y→x[y/M]≡x {M = M} {f = ι}  x≢y
... | .(v y) | refl = *v
\end{code}

\begin{code}
lemmax∙ι≺+x,N : (x : Atom)(N : Λ) → v x ∙ (ι ≺+ (x , N)) ≡ N
lemmax∙ι≺+x,N x N with x ≟ₐ x
... | yes  _    = refl
... | no   x≢x  = ⊥-elim (x≢x refl)
\end{code}

\begin{code}
lemma#→free# : {x : Atom}{σ : Σ}{M : Λ} → x # (M ∙ σ) → x #⇂ (σ , M)
lemma#→free# {x} {σ} {v .y}   x#σy           y *v
  = x#σy
lemma#→free# {x} {σ} {M · N} (#· x#Mσ x#Nσ) y (*·l yfreeMσ)
  = lemma#→free# x#Mσ y yfreeMσ
lemma#→free# {x} {σ} {M · N} (#· x#Mσ x#Nσ) y (*·r yfreeNσ)
  = lemma#→free# x#Nσ y yfreeNσ
lemma#→free# .{Chi' (σ , ƛ z M)} {σ} {ƛ z M} #ƛ≡      y yfreeλzM
  = (χ-lemma2 σ (ƛ z M)) y yfreeλzM
lemma#→free# {x} {σ} {ƛ z M} (#ƛ x#Mσ<+zw)  y (*ƛ yfreeM z≢y)
  with z ≟ₐ y | lemma#→free# x#Mσ<+zw y yfreeM
... | yes z≡y | _  = ⊥-elim (z≢y z≡y)
... | no  _   | hi = hi

lemmafree#→# : {x : Atom}{σ : Σ}{M : Λ} → x #⇂ (σ , M) → x # (M ∙ σ)
lemmafree#→# {x} {σ} {v y}   f = f y *v
lemmafree#→# {x} {σ} {M · N} f
  = #· (lemmafree#→# (λ y yfreeM → f y (*·l yfreeM)))
       (lemmafree#→# (λ y yfreeN → f y (*·r yfreeN)))
lemmafree#→# {x} {σ} {ƛ y M} f
  with Chi' (σ , ƛ y M) | x ≟ₐ Chi' (σ , ƛ y M) | χ-lemma2 σ (ƛ y M)
... | .x | yes refl | x#σ⇂λyM  = #ƛ≡
... | z  | no x≢z   | z#σ⇂λyM  = #ƛ (lemmafree#→# {x} {σ = σ ≺+ (y , v z)} {M} lemma)
   where lemma : (w : Atom) → w * M → x # (σ ≺+ (y , v z)) w
         lemma w wfreeM with y ≟ₐ w
         ... | yes _  = #v (≢-sym x≢z)
         ... | no y≢w = f w (*ƛ wfreeM y≢w)

lemmafree#y→# : {x : Atom}{M : Λ} → ((y : Atom) → y * M → x # v y) → x # M
lemmafree#y→# {x} {v y}   f = f y *v
lemmafree#y→# {x} {M · N} f
  = #· (lemmafree#y→# (λ y yfreeM → f y (*·l yfreeM)))
       (lemmafree#y→# (λ y yfreeN → f y (*·r yfreeN)))
lemmafree#y→# {x} {ƛ y M} f with x ≟ₐ y
lemmafree#y→# {x} {ƛ y M} f
    | no  x≢y = #ƛ (lemmafree#y→# lemma)
  where
  lemma : (u : Atom) → u * M → x # v u
  lemma u ufreeM with y ≟ₐ u
  ... | yes y≡u = #v (λ u≡x → x≢y (trans (sym u≡x) (sym y≡u)))
  ... | no  y≢u = f u (*ƛ ufreeM y≢u)
lemmafree#y→# {x} {ƛ .x M} f
    | yes refl = #ƛ≡
\end{code}

-- No Capture Lemma

\begin{code}
lemmafreeσ→ : {x : Atom}{M : Λ}{σ : Σ} → x * (M ∙ σ) → x *⇂ (σ , M) --∃ (λ y → (y * M) × (x * σ y))
lemmafreeσ→ {x} {v z}   {σ} xfreeσz = z , *v , xfreeσz
lemmafreeσ→ {x} {M · N} {σ} (*·l xfreeMσ) = y , *·l yfreeMσ , xfreeσy
  where y = proj₁ (lemmafreeσ→ {x} {M} xfreeMσ)
        yfreeMσ = proj₁ (proj₂ (lemmafreeσ→ {x} {M} xfreeMσ))
        xfreeσy = proj₂ (proj₂ (lemmafreeσ→ {x} {M} xfreeMσ))
lemmafreeσ→ {x} {M · N} {σ} (*·r xfreeNσ) = y , *·r yfreeNσ , xfreeσy
  where y = proj₁ (lemmafreeσ→ {x} {N} xfreeNσ)
        yfreeNσ = proj₁ (proj₂ (lemmafreeσ→ {x} {N} xfreeNσ))
        xfreeσy = proj₂ (proj₂ (lemmafreeσ→ {x} {N} xfreeNσ))
lemmafreeσ→ {x} {ƛ y M} {σ} (*ƛ xfreeMσ<+yz z≢x)
  with  Chi' (σ , ƛ y M) | proj₁ (lemmafreeσ→ {x} {M} xfreeMσ<+yz)
    | proj₁ (proj₂ (lemmafreeσ→ {x} {M} xfreeMσ<+yz))
    | proj₂ (proj₂ (lemmafreeσ→ {x} {M} xfreeMσ<+yz))
... | z | w | wfreeM | xfreeσ<+yzw  with y ≟ₐ w
... | no  y≢w =  w , *ƛ wfreeM y≢w , xfreeσ<+yzw
... | yes y≡w with xfreeσ<+yzw
lemmafreeσ→ {x} {ƛ y M} {σ} (*ƛ xfreeMσ<+yz z≢x)
    | .x | w | wfreeM | _
    | yes y≡w
    | *v = ⊥-elim (z≢x refl)
--
lemmafreeσ← : {x : Atom}{M : Λ}{σ : Σ} → x *⇂ (σ , M) → x * (M ∙ σ)
lemmafreeσ← {x} {v z}   {σ} (.z , *v       , xfreeσz) = xfreeσz
lemmafreeσ← {x} {M · N} {σ} (y  , *·l yfreeM    , xfreeσy) = *·l (lemmafreeσ← (y , yfreeM , xfreeσy))
lemmafreeσ← {x} {M · N} {σ} (y  , *·r yfreeN    , xfreeσy) = *·r (lemmafreeσ← (y , yfreeN , xfreeσy))
lemmafreeσ← {x} {ƛ z M} {σ} (y  , *ƛ yfreeM z≢y , xfreeσy)
  with Chi' (σ , ƛ z M) | (χ-lemma2 σ (ƛ z M)) y (*ƛ yfreeM z≢y)
... | w | w#σy with w ≟ₐ x
... | no  w≢x = *ƛ (lemmafreeσ← (y , yfreeM , lemma)) w≢x
  where lemma :  x * ((σ ≺+ (z , v w)) y)
        lemma with z ≟ₐ y
        ... | yes z≡y = ⊥-elim (z≢y z≡y)
        ... | no  _   = xfreeσy
lemmafreeσ← {x} {ƛ z M} {σ} (y  , *ƛ yfreeM z≢y , xfreeσy)
  | .x | x#σy | yes refl = ⊥-elim ((lemma-free→¬# xfreeσy) x#σy)
\end{code}


\begin{code}
lemmaz*Mι≺+x,y→z≢x : {x y z : Atom}{M : Λ} → y ≢ z → z * M ∙ (ι ≺+ (x , v y)) → z ≢ x
lemmaz*Mι≺+x,y→z≢x {x} {y}  .{x} {M} y≢x x*Mι≺+x,y refl
  with lemmafreeσ→ {x} {M} {ι ≺+ (x , v y)} x*Mι≺+x,y
... | w , w*M , x*ι≺+x,yw
  with x ≟ₐ w
lemmaz*Mι≺+x,y→z≢x {x} {y}  .{x} {M} y≢x x*Mι≺+x,y refl
    | .x , x*M , *v
    | no   x≢x   = ⊥-elim (x≢x refl)
lemmaz*Mι≺+x,y→z≢x {x} .{x} .{x} {M} x≢x x*Mι≺+x,x refl
    | .x , x*M , *v
    | yes  refl  = ⊥-elim (x≢x refl)

\end{code}

\begin{code}
lemma-subst-σ≡ : {M : Λ}{σ σ' : Σ} →
   (σ , M) ≅⇂ (σ' , M) → (M ∙ σ) ≡ (M ∙ σ')
lemma-subst-σ≡ {v x}   {σ} {σ'} (_ , f)
  = f x *v
lemma-subst-σ≡ {M · N} {σ} {σ'} (_ , f)
  = PropEq.cong₂ _·_
          (lemma-subst-σ≡ {M} (((λ _ x → x) , (λ _ x → x)) , (λ x xfreeM → f x (*·l xfreeM))))
          (lemma-subst-σ≡ {N} (((λ _ x → x) , (λ _ x → x)) , (λ x xfreeN → f x (*·r xfreeN))))
lemma-subst-σ≡ {ƛ x M} {σ} {σ'} (_ , f)
  with Chi' (σ , ƛ x M) | Chi' (σ' , ƛ x M) |
       χ-lemma3 σ σ' (ƛ x M) (ƛ x M) (λ x x*M → (lemma-1 x x*M) , (lemma-2 x x*M)) ((λ _ → id) , (λ _ → id))
  where
  lemma-1 : (w : Atom) → w * ƛ x M → (z : Atom) → z * σ w → z * σ' w
  lemma-1 w wfreeλxM z zfreeσw rewrite f w wfreeλxM = zfreeσw
  lemma-2 : (w : Atom) → w * ƛ x M → (z : Atom) → z * σ' w → z * σ w
  lemma-2 w wfreeλxM z zfreeσ'w rewrite f w wfreeλxM = zfreeσ'w
... | y | .y | refl
  = cong (λ M → ƛ y M) (lemma-subst-σ≡ {M} {σ ≺+ (x , v y)} {σ' ≺+ (x , v y)} (((λ _ x → x) , (λ _ x → x)) , lemma))
  where
  lemma : ((z : Atom) → z * M → (σ ≺+ (x , v y)) z ≡ (σ' ≺+ (x , v y)) z)
  lemma z zfreeM with x ≟ₐ z
  ... | yes _   = refl
  ... | no  x≢z = f  z (*ƛ zfreeM x≢z)
\end{code}

\begin{code}
lemma-length : {M : Λ}{σ : Σ} → ((w : Atom) → length (σ w) ≡ 1) → length M ≡ length (M ∙ σ)
lemma-length {v x}   {σ} p rewrite p x  = refl
lemma-length {M · N} {σ} p
  = PropEq.cong₂ _+_ (lemma-length {M} {σ} p) (lemma-length {N} {σ} p)
lemma-length {ƛ z M} {σ} p with Chi' (σ , ƛ z M)
... | w = cong (λ x → suc x) (lemma-length {M} {σ ≺+ (z , v w)} lemma)
  where
  lemma : (u : Atom) → length ((σ ≺+ (z , v w)) u) ≡ 1
  lemma u with z ≟ₐ u
  ... | yes _ = refl
  ... | no  _ = p u

lemma-length-corolary : {x y : Atom}{M : Λ} → length M ≡ length (M ∙ (ι ≺+ (x , v y)))
lemma-length-corolary {x} {y} {M} = lemma-length {M} {ι ≺+ (x , v y)} lemma
  where
  lemma : (w : Atom) → length ((ι ≺+ (x , v y)) w) ≡ 1
  lemma w with x ≟ₐ w
  ... | yes _ = refl
  ... | no  _ = refl
\end{code}
