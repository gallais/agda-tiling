module Data.Pixel.Tile where

open import Data.Bool.Base using (true)
open import Data.Maybe.Base using (Maybe; fromMaybe)
open import Data.Nat.Base as ℕ using (ℕ)
open import Data.Nat.Bounded.Base
open import Data.Nat.Bounded.Properties using (_≡?_)
open import Data.Sum.Base using ([_,_]′)

open import Relation.Nullary.Decidable using (does)

open import Function.Base using (flip)

open import Level using (Level)

private
  variable
    w wl wr h ht hb : ℕ
    a b c : Level
    A : Set a
    B : Set b
    C : Set c

record Tile (width height : ℕ) {ℓ} (A : Set ℓ) : Set ℓ where
  constructor mkTile
  field runTile : Fin width → Fin height → A
open Tile

map : (A → B) → Tile w h A → Tile w h B
map f tile .runTile k l = f (tile .runTile k l)

zipWith : (A → B → C) → Tile w h A → Tile w h B → Tile w h C
zipWith f tile₁ tile₂ .runTile k l
  = f (tile₁ .runTile k l) (tile₂ .runTile k l)

_◂_ : Tile w h (Maybe A) → Tile w h A → Tile w h A
_◂_ = zipWith (flip fromMaybe)

transpose : Tile w h A → Tile h w A
transpose tile .runTile k l = tile .runTile l k

fill : (w h : ℕ) → A → Tile w h A
fill w h col .runTile k l = col

setPixel : Fin w → Fin h → A → Tile w h A → Tile w h A
setPixel x y px tile .runTile k l with does (k ≡? x) | does (l ≡? y)
... | true | true = px
... | _ | _ = tile .runTile k l

_─_ : Tile w ht A → Tile w hb A → Tile w (ht ℕ.+ hb) A
(top ─ bottom) .runTile k l
  = [ top .runTile k
    , bottom .runTile k
    ]′ (splitAt _ l)


_∣_ : Tile wl h A → Tile wr h A → Tile (wl ℕ.+ wr) h A
(left ∣ right) .runTile k l
  = [ flip (left .runTile) l
    , flip (right .runTile) l
    ]′ (splitAt _ k)
