{-# OPTIONS --guardedness #-}

open import Data.Image
open import Data.Image.IO
open import Data.Maybe using (Maybe; just; nothing; fromMaybe)
open import Data.Nat.Base using ()
open import Data.Image.Pixel using (module RGB8); open RGB8

open import IO.Base
open import IO.Finite

open import Function.Base using (_$_; _∋_)

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


main : Main
main = run do
 savePngImage "test.png"
    $ Image 1500 500 RGB8 ∋_
    $ tile
    $ scale 4
    $ flower
