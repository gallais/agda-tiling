module Data.Image.Pixel where

open import Agda.Builtin.FromNat using (fromNat)

open import Data.Unit.Base using ()
open import Data.Word8.Base using (Word8)
open import Data.Word8.Literals
instance Word8Number = number

{-# FOREIGN GHC import Codec.Picture #-}

module RGB8 where

  record RGB8 : Set where
    constructor [_,_,_]
    field
      red   : Word8
      green : Word8
      blue  : Word8
  {-# COMPILE GHC RGB8 = data PixelRGB8 (PixelRGB8) #-}

  open RGB8 public

  fullred     = [ 255 ,   0 ,   0 ]
  fullgreen   = [   0 , 255 ,   0 ]
  fullblue    = [   0 ,   0 , 255 ]
  navy        = [  16 ,  24 , 107 ]
  azur        = [  16 ,  82 , 214 ]
  cyan        = [ 157 , 247 , 247 ]
  skyblue     = [  74 , 165 , 239 ]
  yellow      = [ 255 , 255 ,  51 ]
  black       = [   0 ,   0 ,   0 ]
  white       = [ 255 , 255 , 255 ]
  purple      = [ 102 ,   0 , 102 ]
  parma       = [ 255 , 153 , 204 ]
  pastelGreen = [ 232 , 249 , 233 ]


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

{-# COMPILE GHC CMYK8 = data PixelCMYK8 (PixelCMYK8) #-}
