module Data.Pixel where

open import Data.Word8.Base using (Word8)


{-# FOREIGN GHC import Codec.Picture #-}

record RGB8 : Set where
  constructor [_,_,_]
  field
    red   : Word8
    green : Word8
    blue  : Word8

{-# COMPILE GHC RGB8 = data PixelRGB8 (PixelRGB8) #-}

record RGBA8 : Set where
  constructor [_,_,_,_]
  field
    red   : Word8
    green : Word8
    blue  : Word8
    alpha : Word8

{-# COMPILE GHC RGBA8 = data PixelRGBA8 (PixelRGBA8) #-}

record CMYK8 : Set where
  constructor [_,_,_,_]
  field
    cyan    : Word8
    magenta : Word8
    yellow  : Word8
    black   : Word8

{-# COMPILE GHC CMYK8 = data PixelCYMK8 (PixelCYMK8) #-}
