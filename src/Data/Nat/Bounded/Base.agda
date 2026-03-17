------------------------------------------------------------------------
-- The Agda standard library
--
-- Bounded Natural numbers (Fin, without the runtime overhead)
------------------------------------------------------------------------

{-# OPTIONS --cubical-compatible --safe #-}

module Data.Nat.Bounded.Base where


open import Data.Bool.Base using (true; false)
import Data.Bool.Properties as Boolₚ
open import Data.Irrelevant as Irrelevant using (Irrelevant; [_])
open import Data.Nat.Base as ℕ using (ℕ; suc; z≤n; z<s; s<s; s<s⁻¹)
import Data.Nat.Properties as ℕₚ
open import Data.Refinement as Refinement using (Refinement; _,_; Refinement-syntax)
open import Data.Sum.Base using (_⊎_; inj₁; inj₂; [_,_]′)

open import Function.Base using (id; _$_; _∘_)
open import Function.Bundles using (Equivalence); open Equivalence using (from)

open import Relation.Binary.PropositionalEquality using (_≡_; refl; cong; subst)
open import Relation.Nullary using (recompute; T?; yes; no)

private
  variable
    m n : ℕ

------------------------------------------------------------------------
-- Types

-- Fin n is a type with n elements.

Fin : ℕ → Set
Fin n = [ m ∈ ℕ ∣ m ℕ.< n ]

nonZero : Fin n → ℕ.NonZero n
nonZero {suc n} k = _

-- Recovering constructors and pattern matching

fzero : ∀ {n} → Fin (suc n)
fzero = 0 , [ z<s ]

fsuc : ∀ {n} → Fin n → Fin (suc n)
fsuc = Refinement.map suc s<s

data View : ∀ {n} (k : Fin n) → Set where
  zero : View {suc n} fzero
  suc  : (k : Fin n) → View (fsuc k)

view : (k : Fin n) → View k
view {suc n} (0 , prf)     = zero
view {suc n} (suc k , prf) = suc (k , Irrelevant.map s<s⁻¹ prf)

unview : {k : Fin n} → View k → Fin n
unview {k = k} _ = k


-- A conversion: toℕ "i" = i.

toℕ : Fin n → ℕ
toℕ = Refinement.value

-- A Fin-indexed variant of Fin.

Fin′ : Fin n → Set
Fin′ i = Fin (toℕ i)

------------------------------------------------------------------------
-- A cast that actually computes on constructors (as opposed to subst)

cast : .(m ≡ n) → Fin m → Fin n
cast {m = m} {n = n} eq
  = Refinement.map id
  $ subst (_ ℕ.<_) (recompute (m ℕₚ.≟ n) eq)

_ : .(eqs : suc m ≡ suc n) →
    cast eqs fzero ≡ fzero
_ = λ eqs → refl

_ : .(eqs : suc m ≡ suc n) .(eq : m ≡ n) (k : Fin m) →
    cast eqs (fsuc k) ≡ fsuc (cast eq k)
_ = λ eqs eq k → refl

------------------------------------------------------------------------
-- Conversions

-- toℕ is defined above.

-- fromℕ n = "n".

fromℕ : (n : ℕ) → Fin (suc n)
fromℕ n = n , [ ℕₚ.n<1+n n ]

-- fromℕ< {m} _ = "m".

fromℕ< : .(m ℕ.< n) → Fin n
fromℕ< m<n = _ , [ m<n ]

-- fromℕ<″ m _ = "m".

open import Relation.Binary using (_⇒_)

<″⇒< : ℕ._<″_ ⇒ ℕ._<_
<″⇒< = ℕₚ.≤″⇒≤

fromℕ<″ : ∀ m {n} → .(m ℕ.<″ n) → Fin n
fromℕ<″ m m<″n = m , [ <″⇒< m<″n ]

------------------------------------------------------------------------
-- Canonical liftings of i:Fin m to larger index

-- injection on the left: "i" ↑ˡ n = "i" in Fin (m + n)

infixl 5 _↑ˡ_
_↑ˡ_ : ∀ {m} → Fin m → ∀ n → Fin (m ℕ.+ n)
_↑ˡ_ {m} i n = Refinement.map id prf i where

  prf : ∀ {k} → k ℕ.< m → k ℕ.< m ℕ.+ n
  prf {k} k<m = let open ℕₚ.≤-Reasoning in begin-strict
    k       ≡⟨ ℕₚ.+-identityʳ k ⟨
    k ℕ.+ 0 <⟨ ℕₚ.+-mono-<-≤ k<m z≤n ⟩
    m ℕ.+ n ∎

-- injection on the right: n ↑ʳ "i" = "n + i" in Fin (n + m)

infixr 5 _↑ʳ_
_↑ʳ_ : ∀ {m} n → Fin m → Fin (n ℕ.+ m)
n ↑ʳ i = Refinement.map (n ℕ.+_) (ℕₚ.+-monoʳ-< n) i

------------------------------------------------------------------------
-- Shrinking

-- reduce≥ "m + i" _ = "i".

reduce≥ : ∀ (i : Fin (m ℕ.+ n)) → .(m ℕ.≤ toℕ i) → Fin n
reduce≥ {m = m} {n = n} (k , prf) m≤i

  = k ℕ.∸ m , (Irrelevant.map go prf Irrelevant.<*> [ m≤i ]) where

  go : k ℕ.< m ℕ.+ n → m ℕ.≤ k → k ℕ.∸ m ℕ.< n
  go k<m+n m≤k = let open ℕₚ.≤-Reasoning in begin-strict
    k ℕ.∸ m       <⟨ ℕₚ.∸-monoˡ-< k<m+n m≤k ⟩
    m ℕ.+ n ℕ.∸ m ≡⟨ ℕₚ.m+n∸m≡n m n ⟩
    n             ∎




-- A strengthening injection into the minimal Fin fibre.

strengthen : ∀ (i : Fin n) → Fin′ (fsuc i)
strengthen (k , prf) = (k , [ ℕₚ.≤-refl ])


-- splitAt m "i" = inj₁ "i"      if i < m
--                 inj₂ "i - m"  if i ≥ m
-- This is dual to splitAt from Data.Vec.

splitAt : ∀ m {n} → Fin (m ℕ.+ n) → Fin m ⊎ Fin n
splitAt m i@(k , prf) with T? (k ℕ.<ᵇ m)
... | yes k<ᵇm = inj₁ (k , [ ℕₚ.<ᵇ⇒< k m k<ᵇm ])
... | no  k≮ᵇm = inj₂ (reduce≥ i (ℕₚ.≮⇒≥ (k≮ᵇm ∘ ℕₚ.<⇒<ᵇ)))


-- inverse of above function
join : ∀ m n → Fin m ⊎ Fin n → Fin (m ℕ.+ n)
join m n = [ _↑ˡ n , m ↑ʳ_ ]′



-- opposite "i" = "pred n - i" (i.e. the additive inverse).

opposite : Fin n → Fin n
opposite {n} i@(k , prf)
  = n ℕ.∸ suc k
  , [ ℕₚ.m<n+o⇒m∸n<o n (suc k) {n} ⦃ nonZero i ⦄ (ℕₚ.m<n+m n z<s) ]
