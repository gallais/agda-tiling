{-# OPTIONS --guardedness #-}

open import Data.Bool.Base using (if_then_else_; _∨_; _∧_)
open import Data.Image
open import Data.Image.IO
open import Data.Maybe using (Maybe; just; nothing; fromMaybe; _<∣>_)
open import Data.Nat.Base as ℕ using (ℕ; suc)
import Data.Nat.Properties as ℕₚ
open import Data.Nat.Bounded.Base using (fromℕ<ᵇ)
open import Data.Nat.Bounded.Properties using (_≡?_; _<?_)
open import Data.Image.Pixel using (module RGB8); open RGB8

open import IO.Base
open import IO.Finite

open import Function.Base using (_$_; _∋_)

open import Level using (Level)

open import Relation.Nullary.Decidable using (does)

flower : Image 30 30 RGB8
flower = border 3 white
       $ quadrants
       $ square ◂ transpose (map (fromMaybe white) square)

  where

  square : Image 12 12 (Maybe RGB8)
  square =
      fill 8 1 nothing ∣ fill 2 1 (just navy) ∣ fill 2 1 nothing
    ─ fill 6 1 nothing ∣ fill 2 1 (just navy) ∣ fill 2 1 (just azur) ∣ fill 1 1 (just navy) ∣ fill 1 1 nothing
    ─ fill 5 3 nothing ∣ fill 1 3 (just navy)
         ∣ (fill 1 1 (just azur) ∣ fill 1 1 (just cyan) ∣ fill 2 1 (just azur) ∣ fill 1 1 (just navy) ∣ fill 1 1 nothing
           ─ (fill 2 2 (just azur) ∣ ((fill 1 1 (just cyan) ∣ fill 2 1 (just skyblue))
                                    ─ (fill 1 1 nothing ∣ fill 1 1 (just cyan) ∣ fill 1 1 (just skyblue))))
              ∣ fill 1 2 (just navy))
    ─ fill 6 2 nothing ∣ fill 1 2 (just navy) ∣ fill 1 2 (just skyblue)
                       ∣ fill 1 2 (just cyan) ∣ fill 1 2 nothing ∣ fill 1 2 (just cyan)
                       ∣ fill 1 2 (just navy)
    ─ fill 7 1 nothing ∣ fill 1 1 (just navy)
                       ∣ fill 1 1 (just skyblue) ∣ fill 1 1 (just cyan) ∣ fill 1 1 (just skyblue)
                       ∣ fill 1 1 (just navy)
    ─ fill 8 1 nothing ∣ fill 1 1 (just navy) ∣ fill 1 1 (just skyblue) ∣ fill 2 1 (just navy)
    ─ fill 9 1 nothing ∣ fill 1 1 (just navy) ∣ fill 2 1 (just yellow)
    ─ fill 9 2 nothing ∣ fill 2 2 (just yellow) ∣ fill 1 2 nothing


private
  variable
    a : Level
    A : Set a
    w wl wr : ℕ
    h ht hb : ℕ

vStitch : Image w (suc ht) (Maybe A)
        → Image w (suc hb) (Maybe A)
        → Image w (suc (ht ℕ.+ hb)) (Maybe A)
vStitch {w = w} {ht = ht} {hb = hb} top bot
  = zipWith _<∣>_
      (top ─ fill w hb nothing)
      (vCast (ℕₚ.+-suc ht hb) $ fill w ht nothing ─ bot)

hStitch : Image (suc wl) h (Maybe A)
        → Image (suc wr) h (Maybe A)
        → Image (suc (wl ℕ.+ wr)) h (Maybe A)
hStitch {wl = wl} {h = h} {wr = wr} lft rgt
  = zipWith _<∣>_
      (lft ∣ fill wr h nothing)
      (hCast (ℕₚ.+-suc wl wr) $ fill wl h nothing ∣ rgt)

grid : Image 33 29 RGB8
grid =
  let line = diagonal 10 1 fullred in
  let tria = vStitch line (vMirror line) in
  let sub = hLine 7 3 (fromℕ<ᵇ {m = 2} _) 1 fullred
             ∣ diagonal 3 1 fullred
  in
  let lft : Image 10 21 _; lft = vStitch tria sub in
  let rct : Image 13 27 _; rct = border 1 (just fullred) (fill 11 25 nothing) in
  let hlf = zipWith _<∣>_
              (fill 16 6 nothing ─ (fill 6 21 nothing ∣ lft))
              (rct ∣ fill 3 27 nothing)
              in
  let ovl = fill 31 9 nothing
        ─ (hLine 10 11 (fromℕ<ᵇ {m = 2} _) 1 fullred
          ∣ (fill 7 2 nothing
            ─ vMirror (diagonal 7 1 fullred)
            ─ fill 7 2 nothing)
          ∣ hLine 8 11 (fromℕ<ᵇ {m = 9} _) 1 fullred
          ∣ fill 6 11 nothing)
        ─ fill 31 7 nothing in
  let ovr = fill 31 9 nothing
        ─ (fill 6 11 nothing
          ∣ hLine 8 11 (fromℕ<ᵇ {m = 9} _) 1 fullred
          ∣ (fill 7 2 nothing
            ─ diagonal 7 1 fullred
            ─ fill 7 2 nothing)
          ∣ hLine 10 11 (fromℕ<ᵇ {m = 2} _) 1 fullred)
        ─ fill 31 7 nothing in


  map (fromMaybe navy)
    $ border 1 nothing
    $ zipWith _<∣>_
        (hStitch hlf (hMirror hlf))
        (zipWith _<∣>_ ovl ovr)


main : Main
main = run do
  savePngImage "flower.png"
    $ Image 960 360 RGB8 ∋_
    $ tile
    $ scale 4
    $ flower
  savePngImage "lozenge.png"
    $ Image 330 290 RGB8 ∋_
    $ tile
    $ scale 5
    $ quadrants
    $ grid
