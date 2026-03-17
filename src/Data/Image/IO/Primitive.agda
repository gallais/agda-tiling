module Data.Image.IO.Primitive where

open import Data.Nat.Base using (ℕ)
open import Data.Image.Pixel using (module RGB8)
open import Data.String.Base using (String)
open import Data.Unit.Base using (⊤)

import IO.Primitive.Core as Prim

open import Level using (0ℓ)

open RGB8

postulate
  primSavePngImage : String → (m n : ℕ) → (ℕ → ℕ → RGB8) → Prim.IO {0ℓ} ⊤

{-# FOREIGN GHC import qualified Data.Text as T #-}
{-# COMPILE GHC primSavePngImage = \ fp m n fun ->
      savePngImage (T.unpack fp)
    $ ImageRGB8
    $ generateImage
      (\ x y -> fun (fromIntegral x) (fromIntegral y))
      (fromInteger m) (fromInteger n)
#-}
