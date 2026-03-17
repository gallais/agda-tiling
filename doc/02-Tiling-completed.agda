{-# OPTIONS --guardedness --erasure --rewriting #-}

------------------------------------------------------------------------
-- Coursework 2: Tiling (100 marks, 60% of course total)
--
-- The goal of this coursework is to write a Domain Specific Language
-- for manipulating images. We will use dependent types to keep track
-- of properties of the images, such as their width and height.
--
------------------------------------------------------------------------

------------------------------------------------------------------------
-- Submission
--
-- Submit by pushing to your private coursework repository. It's
-- easiest to use the same repository as for Coursework 1, but we will
-- cope one way or another.
--
-- Deadline: Thursday 4 April at 5pm
------------------------------------------------------------------------

------------------------------------------------------------------------
-- Life advice
--
-- It is not the case that the hard marks are all at the end of the
-- file, and the easy marks are at the beginning. Consequently, it
-- might be strategic to skip ahead if you get stuck.
------------------------------------------------------------------------

------------------------------------------------------------------------
-- Marks
--
-- Erasure                10 MARKS
-- Fin                    30 MARKS
-- Word8 and Pixel         6 MARKS
-- Image                   4 MARKS
-- Tile                   35 MARKS
-- Extension              15 MARKS
--
-- TOTAL                 100 MARKS
------------------------------------------------------------------------

------------------------------------------------------------------------
-- Imports and variable declarations
------------------------------------------------------------------------

-- If you need to import more things, that's okay, but it hopefully
-- should not be necessary (except for your extension, perhaps)

open import Data.Bool.Base using (Bool; true; false; _∧_; _∨_)
open import Data.Char.Base using (Char)
open import Data.Empty using (⊥; ⊥-elim)
open import Data.List.Base using (List; []; _∷_)
open import Data.Maybe.Base as Maybe
  using (Maybe; nothing; just; fromMaybe; maybe)
open import Data.Nat as ℕ
  using (ℕ; zero; suc; _∸_; _+_; _*_; _<_; s≤s; z<s; s<s; _<?_; NonZero)
import Data.Nat.Literals as ℕ; instance AgdaNumber = ℕ.number

-- /!\ Lots of good stuff in here! -----------
import Data.Nat.Properties as ℕₚ
import Data.Nat.DivMod as ℕₚ
----------------------------------------------

open import Data.String.Base using (String; fromList; _++_)
open import Data.Sum.Base using (_⊎_; inj₁; inj₂)
open import Data.Unit.Base using (⊤; tt)

open import Relation.Nullary using (Irrelevant)
open import Relation.Nullary.Decidable using (Dec; yes; no)
open import Relation.Nullary.Negation using (¬_)
open import Relation.Binary.PropositionalEquality
  using (_≡_; refl; cong; subst; module ≡-Reasoning)
open import Agda.Builtin.Equality.Rewrite

open import Function.Base using (_$_; _∘_; _∋_; case_of_; flip)
open import Axiom.Extensionality.Propositional using (Extensionality)

variable
  A B C : Set

------------------------------------------------------------------------
-- Erasure (10 MARKS)
------------------------------------------------------------------------

-- For an efficient representation of Fin n, we will make use of a
-- recent feature of Agda: Runtime irrelevance. Arguments or record
-- fields marked with "@0" are guaranteed by Agda to have been erased
-- at runtime. Consequently, there are limitions on how such arguments
-- can be used.


-- (1 MARK)
-- Confirm that Agda lets you "unerase" when there is obviously at
-- most one constructor available.
unerase-≡ : ∀ {a} {A : Set a} {@0 x y : A} → @0 x ≡ y → x ≡ y
unerase-≡ refl = refl

unerase-⊥ : @0 ⊥ → ⊥
unerase-⊥ ()

-- What happens if you try to unerase for example Bool?

-- `@0` is not a type former, but we can use a record wrapper to
-- effectively make it one.

record Erased (A : Set) : Set where
  constructor ∣_∣
  field
    @0 erased : A

-- (6 MARKS)
-- Which ones of the following are implementable? Either give an
-- implementation, or a short explanation for why it is not possible.

pure : A → Erased A
pure a = ∣ a ∣

-- extract : Erased A → A
{- Having this would mean that erased things were still available at runtime -}

-- iftenelse : {P : Bool → Set} → (@0 b : Bool) → P true → P false → P b
{- This needs to pattern match on b do decide which branch to take,
but that's obviously not possible at runtime if b is erased -}

erasedExtract : Erased (Erased A → A)
Erased.erased erasedExtract ∣ a ∣ = a
{- It's okay in an erased context -}

unerase-Nat : Erased ℕ → ℕ
unerase-Nat _ = 17

-- erasedNat-correct : (n : ℕ) → unerase-Nat (pure n) ≡ n
{- This would only work if unerase-Nat could look at its argument, but
it cannot if it is not there at runtime -}

module ErasedMonad where
-- (We put this in a module so we don't clash with _>>=_ for IO below)

  -- (2 MARKS)
  -- Show that Erased has the structure of a monad.
  -- Hint: the proofs of the laws should be pleasantly easy.
  _>>=_ : Erased A → (A → Erased B) → Erased B
  _>>=_ ∣ a ∣ f = ∣ f a .erased ∣ where open Erased

  >>=-identityˡ : (a : A) → (f : A → Erased B) → pure a >>= f ≡ f a
  >>=-identityˡ a f = refl

  >>=-identityʳ : (ea : Erased A) → ea >>= pure ≡ ea
  >>=-identityʳ ea = refl

  >>=-assoc : (ea : Erased A) → (f : A → Erased B) → (g : B → Erased C)
            → (ea >>= f) >>= g ≡ (ea >>= λ x → f x >>= g)
  >>=-assoc ea f g = refl

  -- (1 MARK)
  -- Use do-notation to implement the functorial action and the join for
  -- the monad.

  fmap : (A → B) → (Erased A → Erased B)
  fmap f ea = do
    a <- ea
    ∣ f a ∣

  squash : Erased (Erased A) → Erased A
  squash eea = do
    ea <- eea
    ea

------------------------------------------------------------------------
-- Fin (30 MARKS)
------------------------------------------------------------------------

-- We will use Fin n to represent a position within an image that is
-- below the width or height n. For efficiency, we will use an unusual
-- representation of Fin n: rather than a data definition, we will
-- represent Fin n as natural numbers k such that k < n, but, and here
-- is the twist, we will ensure that the proof is not kept around at
-- runtime by marking it as runtime irrelevant.

record Fin (n : ℕ) : Set where
  constructor mkFin
  field
    value : ℕ
    @0 inBounds : value < n

-- (2 MARKS)
-- Implement the usual constructors for Fin.
fzero : ∀ {n} → Fin (suc n)
fzero = mkFin 0 z<s

fsuc : ∀ {n} → Fin n → Fin (suc n)
fsuc (mkFin k prf) = mkFin (suc k) (s<s prf)

-- (1 MARK)
-- Show that fzero ≠ fsuc k for any k.
0≢1+n : ∀ {n} → (k : Fin n) → fzero ≡ fsuc k → ⊥
0≢1+n k ()

-- (1 MARK)
-- Show that fsuc is injective.
fsuc-injective : ∀ {n} → {k l : Fin n} → fsuc k ≡ fsuc l → k ≡ l
fsuc-injective refl = refl

-- (1 MARK)
-- Show that Fin 0 is the empty type, as expected.
¬Fin0 : ¬ (Fin 0)
¬Fin0 ()

-- (2 MARKS)
-- Show that two `Fin n` are equal as soon as their values are equal.
eqFin : ∀ {n} {k l : Fin n} → Fin.value k ≡ Fin.value l → k ≡ l
eqFin {n} {mkFin k p} {mkFin k q} refl with unerase-≡ (ℕₚ.<-irrelevant p q)
... | refl = refl

-- (2 MARKS)
-- Fin 1 is the unit type, as expected. Another way to phrase this is
-- to say that there is an element in Fin 1, and all elements in Fin 1
-- are the same.

Fin1-inhabited : Fin 1
Fin1-inhabited = fzero

Fin1-irrelevant : Irrelevant (Fin 1)
Fin1-irrelevant (mkFin zero p) (mkFin zero q) = eqFin refl
Fin1-irrelevant _ (mkFin (suc w) q) = ⊥-elim (unerase-⊥ (ℕₚ.n≮0 (ℕₚ.≤-pred q)))
Fin1-irrelevant (mkFin (suc v) p) _ = ⊥-elim (unerase-⊥ (ℕₚ.n≮0 (ℕₚ.≤-pred p)))

-- (2 MARKS)
-- Show that Fin n has decidable equality.
_≟_ : ∀ {n} → (k l : Fin n) → Dec (k ≡ l)
(mkFin k p) ≟ (mkFin l q) with k ℕ.≟ l
... | yes k≡l = yes (eqFin k≡l)
... | no ¬k≡l  = no (¬k≡l ∘ cong Fin.value)

-- HARDER (4 MARKS)
-- Show that Fin distributes over +.
split : ∀ {m n} → Fin (m + n) → Fin m ⊎ Fin n
split {m} {n} k with Fin.value k <? m
... | yes k<m = inj₁ (mkFin (Fin.value k) k<m)
... | no ¬k<m = inj₂ (mkFin (Fin.value k ∸ m) p)
  where
    @0 p' : Fin.value k ∸ m < m + n ∸ m
    p' = ℕₚ.∸-monoˡ-< {Fin.value k} {m} {m + n} (Fin.inBounds k) (ℕₚ.≮⇒≥ ¬k<m)

    @0 p : Fin.value k ∸ m < n
    p = subst (Fin.value k ∸ m <_) (ℕₚ.m+n∸m≡n m n) p'

-- HARDER AGAIN (6 MARKS)
-- And show that in fact, split is an isomorphism.
fjoin : ∀ {m n} → Fin m ⊎ Fin n → Fin (m + n)
fjoin {m} {n} (inj₁ k) = mkFin (Fin.value k) (ℕₚ.<-≤-trans (Fin.inBounds k) (ℕₚ.m≤m+n m n))
fjoin {m} {n} (inj₂ k) = mkFin (m + Fin.value k) (ℕₚ.+-monoʳ-< m (Fin.inBounds k))

fjoin-split : ∀ {m} {n} → (k : Fin (m + n)) → fjoin (split {m} {n} k) ≡ k
fjoin-split {m} {n} k with Fin.value k <? m
... | yes k<m = eqFin refl
... | no ¬k<m = eqFin (begin
     m + (Fin.value k ∸ m)
       ≡⟨ ℕₚ.+-∸-assoc m {Fin.value k} {m} (ℕₚ.≮⇒≥ ¬k<m) ⟨
     (m + Fin.value k) ∸ m
       ≡⟨ ℕₚ.m+n∸m≡n m (Fin.value k) ⟩
     Fin.value k
       ∎)
  where open ≡-Reasoning

split-fjoin : ∀ {m n} → (x : Fin m ⊎ Fin n) → split (fjoin x) ≡ x
split-fjoin {m} {n} (inj₁ k) with (Fin.value k <? m)
split-fjoin (inj₁ k) | yes k<m = cong inj₁ (eqFin refl)
split-fjoin (inj₁ k) | no ¬k<m = ⊥-elim (unerase-⊥ (¬k<m (Fin.inBounds k)))
split-fjoin {m} {n} (inj₂ k)  with (m + Fin.value k <? m)
split-fjoin {m} {n} (inj₂ k) | yes m+k<m = ⊥-elim (ℕₚ.m+n≮m m (Fin.value k) m+k<m)
split-fjoin {m} {n} (inj₂ k) | no ¬m+k<m = cong inj₂ (eqFin (ℕₚ.m+n∸m≡n m (Fin.value k)))


-- (2 MARKS)
-- Define the function which sends 0 ↦ m-1, 1 ↦ m-2, ..., m-1 ↦ 0.
complement : ∀ {m} → Fin m → Fin m
complement {m} (mkFin k prf) = mkFin (m ∸ suc k) (step prf) where
  step : ∀ {k m} → k < m → m ∸ suc k < m
  step {k} {suc m} (s≤s prf) = s≤s (ℕₚ.m∸n≤m m k)

-- (3 MARKS)
-- Show that complement is its own inverse.
complement-inverse : ∀ {m} → (k : Fin m) → complement (complement k) ≡ k
complement-inverse {m} k = eqFin $ unerase-≡ (begin
  m ∸ suc (m ∸ suc k')
    ≡⟨⟩
  m ∸ (1 + (m ∸ (1 + k')))
    ≡⟨ ℕₚ.∸-+-assoc m 1 (m ∸ (1 + k')) ⟨
  m ∸ 1 ∸ (m ∸ (1 + k'))
    ≡⟨ cong (m ∸ 1 ∸_) (ℕₚ.∸-+-assoc m 1 k') ⟨
  (m ∸ 1) ∸ ((m ∸ 1) ∸ k')
    ≡⟨ ℕₚ.m∸[m∸n]≡n {m ∸ 1} {k'} (ℕₚ.pred-mono-≤ (Fin.inBounds k)) ⟩
  k'
    ∎)
  where
    k' = Fin.value k
    open ≡-Reasoning


-- (1 MARK)
-- Use remainders of natural numbers and its properties to implement
-- remainders targetting Fin.
_%_ : ℕ → (i : ℕ) → .{{NonZero i}} → Fin i
k % i = mkFin (k ℕ.% i) (ℕₚ.m%n<n k i)

-- (1 MARK)
-- Show that `_% i` is not injective.
%-not-injective : let i = 2
                      k = 1
                      l = 3
                      eq : (k % i) ≡ (l % i)
                      eq = refl
                   in k ≡ l → ⊥
%-not-injective ()


-- Using k % i, we can now allow ourselves to use decimal notation
-- when writing a Fin.

open import Agda.Builtin.FromNat
instance
  FinNumber : ∀ {n} → .{{NonZero n}} → Number (Fin n)
  FinNumber .Number.Constraint k = ⊤
  FinNumber {n} .Number.fromNat k = k % n

private
  -- Try evaluating these:

  testFin : Fin 128
  testFin = 5

  testFin' : Fin 128
  testFin' = 130

-- (2 MARKS)
-- Construct division for Fin, with a precise type.
quot : ∀ {w} i → .{{NonZero i}} → Fin (i * w) → Fin w
quot {w} i (mkFin k prf) = mkFin (k ℕ./ i) (ℕₚ.m<n*o⇒m/o<n $ begin-strict
  k     <⟨ prf ⟩
  i * w ≡⟨ ℕₚ.*-comm i w ⟩
  w * i ∎)
  where open ℕₚ.≤-Reasoning

------------------------------------------------------------------------
-- Word8 and Pixel (6 MARKS)
------------------------------------------------------------------------

-- We will represent pixels as RGB values of Haskell 8-bit words,
-- which we represent in Agda as natural numbers. First we get a bunch
-- of Haskell integration out of the way.

postulate
  Word8 : Set
  toℕ : Word8 → ℕ
  fromℕ' : ℕ → Word8

-- NOTE: Do not use fromℕ', because it does not compute in Agda (only
-- at runtime). Instead use fromℕ (which computes thanks to the
-- rewrite rule below).

abstract
  fromℕ : (n : ℕ) → (@0 p : n < 256) → Word8
  fromℕ n _ = fromℕ' n

postulate
  toℕ-fromℕ : (n : ℕ)(p : n < 256) → toℕ (fromℕ n p) ≡ n
{-# REWRITE toℕ-fromℕ #-}

{-# FOREIGN GHC import Data.Word #-}
{-# COMPILE GHC Word8 = type Word8 #-}
{-# COMPILE GHC fromℕ' = fromInteger #-}
{-# COMPILE GHC toℕ = toInteger #-}

instance
  Word8Number : Number Word8
  Word8Number .Number.Constraint n = ⊤
  Word8Number .Number.fromNat n = fromℕ (n ℕ.% 256) (ℕₚ.m%n<n n 256)

-- Here is our type of pixels.

record Pixel : Set where
  constructor mkPixel
  field
    red : Word8
    green : Word8
    blue : Word8

{-# FOREIGN GHC import Codec.Picture #-}
{-# COMPILE GHC Pixel = data PixelRGB8 (PixelRGB8) #-}

-- And here are some examples of pixels:
fullred fullgreen fullblue navy azur cyan skyblue yellow black white purple parma pastelGreen : Pixel
fullred = mkPixel 255 0 0
fullgreen = mkPixel 0 255 0
fullblue = mkPixel 0 0 255
navy = mkPixel 16 24 107
azur = mkPixel 16 82 214
cyan = mkPixel 157 247 247
skyblue = mkPixel 74 165 239
yellow = mkPixel 255 255 51
black = mkPixel 0 0 0
white = mkPixel 255 255 255
purple = mkPixel 102 0 102
parma = mkPixel 255 153 204
pastelGreen = mkPixel 232 249 233

-- (0 MARKS)
-- Fill in your favourite colour as a pixel here.
myFavouriteColour : Pixel
myFavouriteColour = mkPixel 245 37 37

-- (4 MARKS)
-- For debugging, write a function for displaying an ASCII
-- representation of a pixel. This is the specification:
--
-- If a pixel is black, return '#'.
-- If a pixel is only red, green or blue, you should return an
-- uppercase 'R', 'G' or 'B' respectively.
-- Otherwise return
--   a lowercase 'r' if the pixel is red more than anything else,
--   a lowercase 'g' if it is green  more than anything else,
--   a lowercase 'b' if it is blue  more than anything else,
--   a lowercase 't' if it is most green and blue ("turquoise"),
--   a lowercase 'y' if it is most red and green ("yellow"),
--   a lowercase 'p' if it is most red and blue ("purple"), and
--   a '.' if all colours have the same intensity.

data Cmp : Set where
  LT EQ GT : Cmp

cmp : ℕ → ℕ → Cmp
cmp n m with ℕ.compare n m
... | ℕ.less .n k = LT
... | ℕ.equal .n = EQ
... | ℕ.greater .m k = GT

showPixel : Pixel → Char
showPixel (mkPixel red green blue) with toℕ red | toℕ green | toℕ blue
showPixel (mkPixel red green blue) | 0 | 0 | 0 = '#'
showPixel (mkPixel red green blue) | r | 0 | 0 = 'R'
showPixel (mkPixel red green blue) | 0 | g | 0 = 'G'
showPixel (mkPixel red green blue) | 0 | 0 | b = 'B'
showPixel (mkPixel red green blue) | r | g | b with cmp r g
showPixel (mkPixel red green blue) | r | g | b | LT with cmp g b
showPixel (mkPixel red green blue) | r | g | b | LT | LT = 'b'
showPixel (mkPixel red green blue) | r | g | b | LT | EQ = 't'
showPixel (mkPixel red green blue) | r | g | b | LT | GT = 'g'
showPixel (mkPixel red green blue) | r | g | b | EQ with cmp g b
showPixel (mkPixel red green blue) | r | g | b | EQ | LT = 'b'
showPixel (mkPixel red green blue) | r | g | b | EQ | EQ = '.'
showPixel (mkPixel red green blue) | r | g | b | EQ | GT = 'y'
showPixel (mkPixel red green blue) | r | g | b | GT with cmp r b
showPixel (mkPixel red green blue) | r | g | b | GT | LT = 'b'
showPixel (mkPixel red green blue) | r | g | b | GT | EQ = 'p'
showPixel (mkPixel red green blue) | r | g | b | GT | GT = 'r'

-- Here is a test case to make sure you got it right:
_ : Data.List.Base.map showPixel
                       (fullred ∷ fullgreen ∷ fullblue ∷ navy ∷ azur ∷ cyan ∷ skyblue ∷ yellow ∷ black ∷ white ∷ purple ∷ parma ∷ pastelGreen ∷ [])
  ≡ ('R' ∷ 'G' ∷ 'B' ∷ 'b' ∷ 'b' ∷ 't' ∷ 'b' ∷ 'y' ∷ '#' ∷ '.' ∷ 'p' ∷ 'r' ∷ 'g' ∷ [])
_ = refl

-- (2 MARKS)
-- Is showPixel injective? Either prove it, or produce a
-- counterexample. Comment out the one that does not apply.

-- showPixel-injective : (p p' : Pixel) → showPixel p ≡ showPixel p' → p ≡ p'

showPixel-not-injective : let p  = mkPixel 0 1 3
                              p' = mkPixel 0 2 3
                              eq : showPixel p ≡ showPixel p'
                              eq = refl
                           in p ≡ p' → ⊥
showPixel-not-injective r with cong (toℕ ∘ Pixel.green) r
... | ()

-- Again: prove one, comment out the other. Do not try to prove both.

------------------------------------------------------------------------
-- Image (4 MARKS)
------------------------------------------------------------------------

-- We can represent an image as an assignment of a pixel for each
-- coordinate.

record Image (m n : ℕ) : Set where
  constructor mkImage
  field runImage : Fin m → Fin n → Pixel
open Image

-- (1 MARK)
-- Build some colourful squares.
colourSquare : Pixel → {n : ℕ} → Image n n
colourSquare c = mkImage λ x y → c

redSquare : Image 8 8
redSquare = colourSquare fullred

blueSquare : Image 8 8
blueSquare = colourSquare fullblue

greenSquare : Image 8 8
greenSquare = colourSquare fullgreen

yellowSquare : Image 8 8
yellowSquare = colourSquare yellow

-- (3 MARKS)
-- Use showPixel to show a whole image.
show : {w h : ℕ} → Image w h → String
show {w} {zero} (mkImage fun) = ""
show {w} {suc h} (mkImage fun) = fromList (showRow w (λ x → fun x fzero)) ++ "\n" ++ show {w} {h} (mkImage λ x y → fun x (fsuc y))
  where
    showRow : (n : ℕ) → (Fin n → Pixel) → List Char
    showRow zero f = []
    showRow (suc n) f = showPixel (f fzero) ∷ showRow n (λ x → f (fsuc x))

-- Hint: You can get Agda to print using your show function on a term
--  by doing C-u C-u C-c C-n; easiest is to write a hole, eg
--
--    _ = {!redSquare!}
--
--  and then do C-u C-u C-c C-n in the hole.
--  (The C-u C-u in this case means "use the `show` function in
--  scope".)

-- With a bit more boilerplate, we can call out to the JuicyPixels
-- library in Haskell to save our images in PNG format when running
-- the compiled code:

open import Level using (0ℓ)
open import IO.Base using (IO; lift!; lift; Main; run; _>>=_; _>>_)
open import IO.Finite
import IO.Primitive.Core as Prim

postulate
  primSavePngImage : String → (m n : ℕ) → (ℕ → ℕ → Pixel) → Prim.IO {0ℓ} ⊤

{-# FOREIGN GHC import qualified Data.Text as T #-}
{-# COMPILE GHC primSavePngImage = \ fp m n fun ->
      savePngImage (T.unpack fp)
    $ ImageRGB8
    $ generateImage
      (\ x y -> fun (fromIntegral x) (fromIntegral y))
      (fromInteger m) (fromInteger n)
#-}

savePngImage : {m n : ℕ} → String → Image m n → IO {0ℓ} _
savePngImage {m} {n} fp (mkImage fun)
  = lift! (lift (primSavePngImage fp m n fun′)) where

  cast : (m n : ℕ) → Maybe (Fin m)
  cast 0 _ = nothing
  cast (suc m) zero = just fzero
  cast (suc m) (suc n) = Maybe.map fsuc (cast m n)

  fun′ : (ℕ → ℕ → Pixel)
  fun′ k l with cast m k | cast n l
  ... | just x | just y = fun x y
  ... | _ | _ = mkPixel (fromℕ 0 (s≤s ℕ.z≤n)) (fromℕ 0 (s≤s ℕ.z≤n)) (fromℕ 0 (s≤s ℕ.z≤n))

------------------------------------------------------------------------
-- Tile (35 MARKS)
------------------------------------------------------------------------

-- An image is a 2D array of pixels. We can abstract away from pixels
-- to arbitrary data in some set A:

record Tile (width height : ℕ) (A : Set) : Set where
  constructor mkTile
  field runTile : Fin width → Fin height → A
open Tile

variable
  w w₁ w₂ : ℕ
  h h₁ h₂ : ℕ

-- (1 MARK)
-- Construct a way to change the data stored in a tile.
map : (A → B) → Tile w h A → Tile w h B
map f tile .runTile k l = f (tile .runTile k l)

-- (2 MARKS)
-- State and prove that map preserves identities and composition
-- (pointwise).

map-id : (t : Tile w h A) → map (λ x → x) t ≡ t
map-id t = refl

map-comp : (g : B → C)(f : A → B) → (t : Tile w h A) → map (g ∘ f) t ≡ map g (map f t)
map-comp g f t = refl

-- (1 MARK)
-- Do the same combining data from two tiles, position-wise.
zipWith : (A → B → C) → Tile w h A → Tile w h B → Tile w h C
zipWith f tile₁ tile₂ .runTile k l
  = f (tile₁ .runTile k l) (tile₂ .runTile k l)

-- (1 MARK)
-- Use zipWith to define a combinator for putting one tile in front of
-- the other, where `nothing` signifies holes in the front tile,
-- seeing through to the back tile.
_◂_ : Tile w h (Maybe A) → Tile w h A → Tile w h A
_◂_ = zipWith (flip fromMaybe)

-- (1 MARK)
-- Show that you can flip a tile along its axis.
transpose : Tile w h A → Tile h w A
transpose tile .runTile k l = tile .runTile l k

-- (1 MARK)
-- Show that you can fill an arbitrary tile with a fixed colour.
fill : (w h : ℕ) → A → Tile w h A
fill w h col .runTile k l = col

-- HARD (4 MARKS)
-- Show that you can merge together two layers of tiles into one layer.
join : Tile w₁ h₁ (Tile w₂ h₂ A) → Tile (w₁ * w₂) (h₁ * h₂) A
runTile (join {w₁ = w₁} {h₁ = h₁} {w₂ = zero} {h₂ = h₂} (mkTile fun)) k l = ⊥-elim (¬Fin0 (subst Fin (ℕₚ.*-comm w₁ 0) k))
runTile (join {w₁ = w₁} {h₁ = h₁} {w₂ = w₂} {h₂ = zero} (mkTile fun)) k l = ⊥-elim (¬Fin0 (subst Fin (ℕₚ.*-comm h₁ 0) l))
runTile (join {w₁ = w₁} {h₁ = h₁} {w₂ = w₂@(suc _)} {h₂ = h₂@(suc _)} (mkTile fun)) k l = fun k₁ l₁ .runTile k₂ l₂
  where
    k₁ = quot w₂ (subst Fin (ℕₚ.*-comm w₁ w₂) k)
    k₂ = Fin.value k % w₂
    l₁ = quot h₂ (subst Fin (ℕₚ.*-comm h₁ h₂) l)
    l₂ = Fin.value l % h₂

-- (1 MARK)
-- Images are basically the same things as tiles of pixels.
fromImage : Image w h → Tile w h Pixel
fromImage (mkImage fun) = mkTile fun

toImage : Tile w h Pixel → Image w h
toImage (mkTile fun) = mkImage fun

-- (2 MARKS)
-- Given a coordinate x y and a tile of pixels, we can
-- create an image focused at that coordinate (wrapping around if the
-- coordinate is too large). This gives us the basics of tiling!
focusAt : ∀ {i j} → .{{NonZero i}} → .{{NonZero j}} →
          ℕ → ℕ → Tile i j Pixel → Image w h
focusAt {i = i} {j} x y tile .runImage k l
  = runTile tile
      ((Fin.value k + suc i ∸ (x ℕ.% i)) % i)
      ((Fin.value l + suc j ∸ (y ℕ.% j)) % j)

-- (1 MARK)
-- In particular, use focusAt to convert from tiles of pixels to images
-- in a "wrapping around" way
wrapTile : ∀ {i j} → Tile (suc i) (suc j) Pixel → Image w h
wrapTile = focusAt 0 0

-- (1 MARK)
-- Given a coordinate in a tile, we can also change the value at that
-- particular coordinate.
setPixel : Fin w → Fin h → A → Tile w h A → Tile w h A
setPixel x y px tile .runTile k l with k ≟ x | l ≟ y
... | yes _ | yes _ = px
... | _ | _ = tile .runTile k l

-- Here is a test case you can try to show (C-u C-u C-c C-n almostRedSquare):
almostRedSquare : Image 8 8
almostRedSquare = toImage (setPixel 1 3 fullblue (fromImage redSquare))

-- HARD, BECAUSE AGDA CAN BE CLUNKY (4 MARKS)
-- Show that, assuming function extensionality, setting the same pixel
-- twice overwrites the first attempt.
setPixel-setPixel : (ext : Extensionality 0ℓ 0ℓ)
                  → (x : Fin w) → (y : Fin h) → (a a' : A) → (t : Tile w h A)
                  → setPixel x y a (setPixel x y a' t) ≡ setPixel x y a t
setPixel-setPixel ext x y a a' t = eqTile _ _ (ext λ x → ext λ y → lemma x y)
  where
    eqTile : (t t' : Tile w h A) → runTile t ≡ runTile t' → t ≡ t'
    eqTile t t' refl = refl

    lemma : ∀ k l → runTile (setPixel x y a (setPixel x y a' t)) k l ≡ runTile (setPixel x y a t) k l
    lemma k l with k ≟ x in eq₁ | l ≟ y in eq₂
    ... | yes _ | yes _ = refl
    ... | yes _ | no _ rewrite eq₁ rewrite eq₂ = refl
    ... | no  _ | yes _ rewrite eq₁ rewrite eq₂ = refl
    ... | no  _ | no _ rewrite eq₁ rewrite eq₂ = refl

-- (2 MARKS)
-- Show that we can scale a tile both horizontally and vertically.
hScale : ∀ i → Tile w h A → Tile (i * w) h A
hScale 0 tile .runTile k l = ⊥-elim (¬Fin0 k)
hScale i@(suc _) tile .runTile k l = tile .runTile (quot i k) l

vScale : ∀ i → Tile w h A → Tile w (i * h) A
vScale 0 tile .runTile k l = ⊥-elim (¬Fin0 l)
vScale i@(suc _) tile .runTile k l = tile .runTile k (quot i l)

-- (1 MARK)
-- Use hScale and vScale to scale in both dimensions at the same time.
scale : ∀ i → Tile w h A → Tile (i * w) (i * h) A
scale i = hScale i ∘ vScale i


-- Test case:
scaledSquare : Image 16 16
scaledSquare = toImage (scale 2 (fromImage greenSquare))

-- (3 MARKS)
-- Show how to put one tile above another, or one to the right of another.
infixr 2 _─_
infixr 3 _∥_

_─_ : Tile w h₁ A → Tile w h₂ A → Tile w (h₁ + h₂) A
(top ─ bottom) .runTile k l = case split l of λ where
  (inj₁ l) → top .runTile k l
  (inj₂ l) → bottom .runTile k l

redGreenSquare : Image 8 16
redGreenSquare = toImage (fromImage redSquare ─ fromImage greenSquare)

_∥_ : Tile w₁ h A → Tile w₂ h A → Tile (w₁ + w₂) h A
(left ∥ right) .runTile k l = case split k of λ where
  (inj₁ k) → left .runTile k l
  (inj₂ k) → right .runTile k l

greenBlueSquare : Image 16 8
greenBlueSquare = toImage (fromImage greenSquare ∥ fromImage blueSquare)

gbrgSquare : Image 16 16
gbrgSquare = toImage $ (fromImage greenSquare ∥ fromImage blueSquare) ─ (fromImage redSquare ∥ fromImage greenSquare)


-- (2 MARKS)
-- Construct mirroring horizontally and vertically.
hMirror : Tile w h A → Tile w h A
hMirror tile .runTile k l = tile .runTile (complement k) l

vMirror : Tile w h A → Tile w h A
vMirror tile .runTile k l = tile .runTile k (complement l)

grbgSquare : Image 16 16
grbgSquare = toImage $ hMirror $ vMirror $ fromImage $ gbrgSquare

-- (2 MARKS)
-- Use ─ and ∥ to make an i pixels wide border around a given tile.
border : (i : ℕ) → A → Tile w h A → Tile (i + (w + i)) (i + (h + i)) A
border i col tile
  = fill _ i col
  ─ fill i _ col ∥ tile ∥ fill i _ col
  ─ fill _ i col

borderedSquare : Image 20 20
borderedSquare = toImage $ border 2 black $ fromImage gbrgSquare

-- (2 MARKS)
-- Take the top left quadrant and produce a full rectangle by
-- symmetries: e.g.  if the tile is the image '⬀', quadrants should
-- produce the image
--
--    ⬀⬁
--    ⬂⬃
--
quadrants : Tile w h A → Tile (w + w) (h + h) A
quadrants tile = horizontal ─ vMirror horizontal where
  horizontal = tile ∥ hMirror tile

quadborderedSquare : Image 40 40
quadborderedSquare = toImage $ quadrants $ fromImage borderedSquare

-- (3 MARKS)
-- Using the combinators you have written, create your own image!
-- Try to make it look nice.
myImage : Image 64 64
myImage = toImage $ quadrants (mkTile diag ◂ mkTile blue)
  where
    blue : Fin 32 → Fin 32 → Pixel
    blue x y = mkPixel 0 0 (fromℕ ((255 * Fin.value x) ℕ./ 32) (ℕₚ.m<n*o⇒m/o<n {255 * Fin.value x} {256} {32} (ℕₚ.*-mono-< {255} ℕₚ.≤-refl (Fin.inBounds x))))
    diag : Fin 32 → Fin 32 → Maybe Pixel
    diag x y with ℕ.∣ Fin.value x - Fin.value y ∣ ℕ.<ᵇ 3
    ... | true = just white
    ... | false = nothing


-- Here is a more complicated tile using most of the things you have produced so far.
flower : Tile 30 30 Pixel
flower = border 3 white
       $ quadrants
       $ square ◂ transpose (map (fromMaybe white) square)

  where

  square : Tile 12 12 (Maybe Pixel)
  square =
      fill 8 1 nothing ∥ fill 2 1 (just navy) ∥ fill 2 1 nothing
    ─ fill 6 1 nothing ∥ fill 2 1 (just navy) ∥ fill 2 1 (just azur) ∥ fill 1 1 (just navy) ∥ fill 1 1 nothing
    ─ fill 5 3 nothing ∥ fill 1 3 (just navy)
         ∥ (fill 1 1 (just azur) ∥ fill 1 1 (just cyan) ∥ fill 2 1 (just azur) ∥ fill 1 1 (just navy) ∥ fill 1 1 nothing
           ─ (fill 2 2 (just azur) ∥ ((fill 1 1 (just cyan) ∥ fill 2 1 (just skyblue))
                                    ─ (fill 1 1 nothing ∥ fill 1 1 (just cyan) ∥ fill 1 1 (just skyblue))))
              ∥ fill 1 2 (just navy))
    ─ fill 6 2 nothing ∥ fill 1 2 (just navy) ∥ fill 1 2 (just skyblue)
                       ∥ fill 1 2 (just cyan) ∥ fill 1 2 nothing ∥ fill 1 2 (just cyan)
                       ∥ fill 1 2 (just navy)
    ─ fill 7 1 nothing ∥ fill 1 1 (just navy)
                       ∥ fill 1 1 (just skyblue) ∥ fill 1 1 (just cyan) ∥ fill 1 1 (just skyblue)
                       ∥ fill 1 1 (just navy)
    ─ fill 8 1 nothing ∥ fill 1 1 (just navy) ∥ fill 1 1 (just skyblue) ∥ fill 2 1 (just navy)
    ─ fill 9 1 nothing ∥ fill 1 1 (just navy) ∥ fill 2 1 (just myFavouriteColour)
    ─ fill 9 2 nothing ∥ fill 2 2 (just myFavouriteColour) ∥ fill 1 2 nothing


-- Here is another example. It wraps nicely!
testTile : Tile 22 22 Pixel
testTile = quadrants base+ where

  empty : ∀ {m} → Tile m 1 Pixel
  empty .runTile k l = pastelGreen

  base : Tile 10 10 Pixel
  base .runTile k l = case k ≟ l of λ where
    (yes k≡l) → black
    (no ¬k≡l) → pastelGreen

  base+ : Tile 11 11 Pixel
  base+ = setPixel 0 10 purple
        $ setPixel 1 9 parma
        $ setPixel 2 9 purple
        $ setPixel 1 8 purple
        $ transpose empty ∥ setPixel 9 0 black base ─ empty

-- And here is a more basic base tile for wrapping.
baseTile : Tile 10 1 Pixel
baseTile = leftmost ∥ hMirror leftmost where

  leftmost : Tile 5 1 Pixel
  leftmost = (Tile 1 1 Pixel ∋ mkTile (λ _ _ → white)) ∥ mkTile (λ _ _ → black)

------------------------------------------------------------------------
-- Main function
------------------------------------------------------------------------

main : Main
main = run do
     savePngImage "test.png"
        $ Image 1500 500 ∋_
        $ wrapTile
        $ scale 4
        $ flower
     savePngImage "test2.png"
        $ Image 1500 500 ∋_
        $ wrapTile
        $ scale 4
        $ testTile
     savePngImage "test3.png"
        $ Image 160 160 ∋_
        $ toImage
        $ scale 10
        $ fromImage redSquare ∥ fromImage greenSquare
          ─
          fromImage blueSquare ∥ fromImage yellowSquare
     savePngImage "myImage.png" myImage

-- Feel free to play around with the main function. You probably want
-- to at least save your image as a PNG as well!

------------------------------------------------------------------------
-- Extend the project (15 MARKS)
------------------------------------------------------------------------

-- Again the final marks will be awarded for interesting extensions to
-- the above program. You might want to include a simple command line
-- interface for selecting which file to save to. Here are some other
-- ideas for what you could do:
-- * Rather than just writing images, you could dig into the JuicyPixels API [1]
--   and also support reading images
-- * Write a combinator for nesting an image into itself
-- * Implements image effects such as blur, staggered columns/rows, fade, ...
--
-- Marks will be awarded based on how interesting the program is, how
-- elegant and readable the code is, and for making good use of the
-- type system.
--
-- [1] https://hackage.haskell.org/package/JuicyPixels
