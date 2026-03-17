------------------------------------------------------------------------
-- The Agda standard library
--
-- Properties of bounded Natural numbers
------------------------------------------------------------------------

{-# OPTIONS --cubical-compatible --safe #-}

module Data.Nat.Bounded.Properties where

open import Data.Nat as ℕ using (ℕ)
open import Data.Nat.Bounded.Base
open import Data.Refinement as Refinement using (_,_)

open import Function.Base using (_∘_)

open import Relation.Binary.Definitions using (DecidableEquality)
open import Relation.Binary.PropositionalEquality using (_≡_; _≢_; cong; refl)
import Relation.Nullary.Decidable.Core as Dec
open import Relation.Nullary.Negation.Core using (¬_)

private
  variable
    m n : ℕ
    k : Fin n

0≢1+k : ∀ {n} → (k : Fin n) → fzero ≢ fsuc k
0≢1+k k ()

fsuc-injective : ∀ {n} {k l : Fin n} → fsuc k ≡ fsuc l → k ≡ l
fsuc-injective {k = kv , kprf} {l = lv , lprf} refl = cong (kv ,_) refl

¬Fin0 : ¬ (Fin 0)
¬Fin0 ()

eqFin : ∀ {n} {k l : Fin n} → Refinement.value k ≡ Refinement.value l → k ≡ l
eqFin {n} {k , p} {k , q} refl = refl


_≡?_ : DecidableEquality (Fin n)
(k , p) ≡? (l , q) = Dec.map′ eqFin (cong Refinement.value) (k ℕ.≟ l)
