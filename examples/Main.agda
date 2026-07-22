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

empty : (w h : ℕ) → Image w h (Maybe A)
empty w h = fill w h nothing

grid : Image 33 29 RGB8
grid =
  let line = diagonal 10 1 fullred in
  let tria = vStitch line (vMirror line) in
  let sub = hLine 7 3 (fromℕ<ᵇ {m = 2} _) 1 fullred
             ∣ diagonal 3 1 fullred
  in
  let lft : Image 10 21 _; lft = vStitch tria sub in
  let rct : Image 13 27 _; rct = border 1 (just fullred) (empty 11 25) in
  let hlf = zipWith _<∣>_
              (empty 16 6 ─ (empty 6 21 ∣ lft))
              (rct ∣ empty 3 27)
              in
  let ovl = empty 31 9
        ─ (hLine 10 11 (fromℕ<ᵇ {m = 2} _) 1 fullred
          ∣ (empty 7 2
            ─ vMirror (diagonal 7 1 fullred)
            ─ empty 7 2)
          ∣ hLine 8 11 (fromℕ<ᵇ {m = 9} _) 1 fullred
          ∣ empty 6 11)
        ─ empty 31 7 in
  let ovr = empty 31 9
        ─ (empty 6 11
          ∣ hLine 8 11 (fromℕ<ᵇ {m = 9} _) 1 fullred
          ∣ (empty 7 2
            ─ diagonal 7 1 fullred
            ─ empty 7 2)
          ∣ hLine 10 11 (fromℕ<ᵇ {m = 2} _) 1 fullred)
        ─ empty 31 7 in


  map (fromMaybe navy)
    $ border 1 nothing
    $ zipWith _<∣>_
        (hStitch hlf (hMirror hlf))
        (zipWith _<∣>_ ovl ovr)

glamis : Image _ _ RGB8
glamis =
  let box = border 1 nothing
           $ (((diagonal 30 4 navy ∣ hLine 20 30 (fromℕ<ᵇ {m = 0} _) 4 navy)
             ─ vLine 50 40 (fromℕ<ᵇ {m = 0} _) 4 navy)
             ∣ (vLine 4 50 (fromℕ<ᵇ {m = 0} _) 4 navy ─ empty 4 20))
             ─ (hLine 30 4 (fromℕ<ᵇ {m = 0} _) 4 navy ∣ empty 24 4)

  in
  let arc = disc 56 76 (fromℕ<ᵇ {m = 54} _) (fromℕ<ᵇ {m = 74} _) 24 navy in
  let quad = zipWith _<∣>_ (empty 56 68 ─ empty 48 8 ∣
                            (vLine 8 4 (fromℕ<ᵇ {m = 7} _) 4 skyblue
                             ─ hLine 8 4 (fromℕ<ᵇ {m = 0} _) 4 skyblue))
           $ zipWith _<∣>_ arc box
  in
  let half = hStitch quad (hMirror quad) in
  scale 1
    $ map (fromMaybe skyblue)
    $ vStitch half (vMirror half)


stripes : (h : ℕ) → A → Image 6 (3 ℕ.+ h) (Maybe A)
stripes h col = vMirror $
  ((fill 3 3 nothing ∣ translate 3 0 (diagonal 3 1 (just col)))
     ─ tile {w = 6} (diagonal 6 1 (just col)))
  ◂ ((tile {w = 6} (diagonal 6 1 (just col)))
  ◂ (hMirror (fill 5 1 nothing ∣ fill 1 1 (just col) ─ fill 6 (2 ℕ.+ h) nothing)))

tartan : Image 48 48 RGB8
tartan
  = ( fill 1 48 (just black)
    ∣ stripes 45 fullblue
    ∣ stripes 45 fullblue
    ∣ fill 1 48 (just black)
    ∣ fill 6 48 nothing
    ∣ fill 1 48 (just black)
    ∣ stripes 45 fullblue
    ∣ fill 1 48 (just black)
    ∣ fill 20 48 nothing
    )
    ◂ ((fill 48 1 (just orange) ─ translate 0 1 (transpose (stripes 45 yellow)) ─ fill 48 1 (just orange) ─ fill 48 40 nothing)
    ◂ fill 48 48 navy)

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
  savePngImage "glamis.png"
    $ Image 1024 1024 RGB8 ∋_
    $ focusAt 100 100
    $ glamis
  savePngImage "tartan.png"
    $ Image 1600 1600 RGB8 ∋_
    $ tile
    $ scale 5
    $ tartan
