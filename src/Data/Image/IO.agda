{-# OPTIONS --guardedness #-}

module Data.Image.IO where

open import Data.Bool.Properties using (T?)
open import Data.Image using (Image; mkImage)
open import Data.Maybe.Base using (Maybe; nothing; just)
open import Data.Nat.Base as ℕ using (ℕ)
open import Data.Nat.Bounded.Base using (Fin; fromℕ<ᵇ)
open import Data.Image.Pixel using (module RGB8)
open import Data.String.Base using (String)

open import IO.Base using (IO; lift!; lift)

open import Level using (0ℓ)

open import Relation.Nullary.Decidable using (yes; no)

open RGB8

import Data.Image.IO.Primitive as Prim

savePngImage : {m n : ℕ} → String → Image m n RGB8 → IO {0ℓ} _
savePngImage {m} {n} fp (mkImage fun)
  = lift! (lift (Prim.primSavePngImage fp m n fun′)) where

  cast : (m n : ℕ) → Maybe (Fin m)
  cast m n with T? (n ℕ.<ᵇ m)
  ... | yes p = just (fromℕ<ᵇ p)
  ... | no _ = nothing

  fun′ : (ℕ → ℕ → RGB8)
  fun′ k l with cast m k | cast n l
  ... | just x | just y = fun x y
  ... | _ | _ = black
