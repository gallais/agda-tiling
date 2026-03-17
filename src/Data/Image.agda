module Data.Image where

open import Data.Bool.Base using (true)
open import Data.Empty using (⊥-elim)
open import Data.Maybe.Base using (Maybe; fromMaybe)
open import Data.Nat.Base as ℕ using (ℕ; suc; NonZero)
import Data.Nat.Properties as ℕₚ
open import Data.Nat.Bounded.Base as Fin using (Fin; quot; _%_; splitAt; opposite)
open import Data.Nat.Bounded.Properties using (¬Fin0; _≡?_)
open import Data.Sum.Base using ([_,_]′)

open import Relation.Binary.PropositionalEquality using (subst)
open import Relation.Nullary.Decidable using (does)

open import Function.Base using (_$_; _∘_; flip)

open import Level using (Level)

private
  variable
    w wl wr h ht hb : ℕ
    a b c : Level
    A : Set a
    B : Set b
    C : Set c

record Image (width height : ℕ) {ℓ} (A : Set ℓ) : Set ℓ where
  constructor mkImage
  field runImage : Fin width → Fin height → A
open Image public

map : (A → B) → Image w h A → Image w h B
map f tile .runImage k l = f (tile .runImage k l)

zipWith : (A → B → C) → Image w h A → Image w h B → Image w h C
zipWith f tile₁ tile₂ .runImage k l
  = f (tile₁ .runImage k l) (tile₂ .runImage k l)

_◂_ : Image w h (Maybe A) → Image w h A → Image w h A
_◂_ = zipWith (flip fromMaybe)

transpose : Image w h A → Image h w A
transpose tile .runImage k l = tile .runImage l k

fill : (w h : ℕ) → A → Image w h A
fill w h px .runImage _ _ = px

join : Image wl ht (Image wr hb A) → Image (wl ℕ.* wr) (ht ℕ.* hb) A
runImage (join {wl = wl} {wr = 0} _) k l = ⊥-elim (¬Fin0 (subst Fin (ℕₚ.*-comm wl 0) k))
runImage (join {ht = ht} {hb = 0} _) k l = ⊥-elim (¬Fin0 (subst Fin (ℕₚ.*-comm ht 0) l))
runImage (join {wl = wl} {ht = ht} {wr = wr@(suc _)} {hb = hb@(suc _)} tile) k l
  = tile .runImage k₁ l₁ .runImage k₂ l₂
  where
    k₁ = quot wr (subst Fin (ℕₚ.*-comm wl wr) k)
    k₂ = Fin.toℕ k % wr
    l₁ = quot hb (subst Fin (ℕₚ.*-comm ht hb) l)
    l₂ = Fin.toℕ l % hb

focusAt : ∀ {i j} → .{{NonZero i}} → .{{NonZero j}} →
          ℕ → ℕ → Image i j A → Image w h A
focusAt {i = i} {j} x y tile .runImage k l
  = runImage tile
      ((Fin.toℕ k ℕ.+ suc i ℕ.∸ (x ℕ.% i)) % i)
      ((Fin.toℕ l ℕ.+ suc j ℕ.∸ (y ℕ.% j)) % j)

tile : ∀ {i j} → .{{NonZero i}} → .{{NonZero j}} → Image i j A → Image w h A
tile = focusAt 0 0

setPixel : Fin w → Fin h → A → Image w h A → Image w h A
setPixel x y px tile .runImage k l with does (k ≡? x) | does (l ≡? y)
... | true | true = px
... | _ | _ = tile .runImage k l

hScale : ∀ i → Image w h A → Image (i ℕ.* w) h A
hScale 0 tile .runImage k l = ⊥-elim (¬Fin0 k)
hScale i@(suc _) tile .runImage k l = tile .runImage (quot i k) l

vScale : ∀ i → Image w h A → Image w (i ℕ.* h) A
vScale 0 tile .runImage k l = ⊥-elim (¬Fin0 l)
vScale i@(suc _) tile .runImage k l = tile .runImage k (quot i l)

-- (1 MARK)
-- Use hScale and vScale to scale in both dimensions at the same time.
scale : ∀ i → Image w h A → Image (i ℕ.* w) (i ℕ.* h) A
scale i = hScale i ∘ vScale i

infixr 2 _─_
_─_ : Image w ht A → Image w hb A → Image w (ht ℕ.+ hb) A
(top ─ bottom) .runImage k l
  = [ top .runImage k
    , bottom .runImage k
    ]′ (splitAt _ l)

infixr 3 _∣_
_∣_ : Image wl h A → Image wr h A → Image (wl ℕ.+ wr) h A
(left ∣ right) .runImage k l
  = [ flip (left .runImage) l
    , flip (right .runImage) l
    ]′ (splitAt _ k)

hMirror : Image w h A → Image w h A
hMirror tile .runImage k l = tile .runImage (opposite k) l

vMirror : Image w h A → Image w h A
vMirror tile .runImage k l = tile .runImage k (opposite l)

border : (i : ℕ) → A → Image w h A → Image (i ℕ.+ (w ℕ.+ i)) (i ℕ.+ (h ℕ.+ i)) A
border i col tile
  = fill _ i col
  ─ fill i _ col ∣ tile ∣ fill i _ col
  ─ fill _ i col

-- Taking the top left quadrant and producing a full rectangle by
-- symmetries: e.g.  if the tile is the image '⬀', quadrants
-- produces the image
--
--    ⬀⬁
--    ⬂⬃
--
quadrants : Image w h A → Image (w ℕ.+ w) (h ℕ.+ h) A
quadrants tile = horizontal ─ vMirror horizontal where
  horizontal = tile ∣ hMirror tile
