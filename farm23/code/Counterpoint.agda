module Counterpoint where

open import Data.Nat
  using (ℕ; zero; suc; _∸_; compare; equal)
  renaming (_+_ to _+ℕ_)
open import Data.Integer
  using (ℤ; _⊖_; _*_)
  renaming (+_ to pos; -[1+_] to negsuc; _+_ to _+ℤ_)
open import Data.Bool using (Bool; true; false; not)
open import Data.Product using (_×_; _,_; proj₁; proj₂)
open import Data.List using (List; []; _∷_; foldr)

-- A pitch is one of the 13 pitches in the C major scale
data Pitch : Set where
  c  : Pitch
  c# : Pitch
  d  : Pitch
  d# : Pitch
  e  : Pitch
  f  : Pitch
  f# : Pitch
  g  : Pitch
  g# : Pitch
  a  : Pitch
  a# : Pitch
  b  : Pitch
  c₂ : Pitch

-- An interval is the distance between two notes within an octave
data Interval : Set where
  uni  : Interval
  min2 : Interval
  maj2 : Interval
  min3 : Interval
  maj3 : Interval
  per4 : Interval
  aug4 : Interval
  per5 : Interval
  min6 : Interval
  maj6 : Interval
  min7 : Interval
  maj7 : Interval
  oct  : Interval

-- A bar in first species counterpoint is a pair of a pitch and an interval
PI : Set
PI = Pitch × Interval

-- A direction tells us whether a line goes up, stays the same, or goes down
data Direction : Set where
  upward   : Direction
  same     : Direction
  downward : Direction

-- Conversion between pitches / intervals and natural numbers
pton : Pitch → ℕ
pton c  = 1
pton c# = 2
pton d  = 3
pton d# = 4
pton e  = 5
pton f  = 6
pton f# = 7
pton g  = 8
pton g# = 9
pton a  = 10
pton a# = 11
pton b  = 12
pton c₂ = 13

ntop : ℕ → Pitch
ntop 1  = c
ntop 2  = c#
ntop 3  = d
ntop 4  = d#
ntop 5  = e
ntop 6  = f
ntop 7  = f#
ntop 8  = g
ntop 9  = g#
ntop 10 = a
ntop 11 = a#
ntop 12 = b
ntop 13 = c₂
ntop _  = c₂ -- dummy

iton : Interval → ℕ
iton uni  = 1
iton min2 = 2
iton maj2 = 3
iton min3 = 4
iton maj3 = 5
iton per4 = 6
iton aug4 = 7
iton per5 = 8
iton min6 = 9
iton maj6 = 10
iton min7 = 11
iton maj7 = 12
iton oct  = 13

ntoi : ℕ → Interval
ntoi 1  = uni
ntoi 2  = min2
ntoi 3  = maj2
ntoi 4  = min3
ntoi 5  = maj3
ntoi 6  = per4
ntoi 7  = aug4
ntoi 8  = per5
ntoi 9  = min6
ntoi 10 = maj6
ntoi 11 = min7
ntoi 12 = maj7
ntoi 13 = oct
ntoi _  = oct -- dummy

int : Pitch → Pitch → Interval
int p₁ p₂ = ntoi ((pton p₁) ∸ (pton p₂) +ℕ 1)

cpitch : PI → Pitch
cpitch pi = ntop ((pton (proj₁ pi)) +ℕ (iton (proj₂ pi) ∸ 1))

-- Whether the counterpoint note is a chromatic note
-- (i.e., not a member of the C major scale)
chromatic : PI → Bool
chromatic pi with cpitch pi
... | c  = false
... | c# = true
... | d  = false
... | d# = true
... | e  = false
... | f  = false
... | f# = true
... | g  = false
... | g# = true
... | a  = false
... | a# = true
... | b  = false
... | c₂ = false

-- Whether an interval is dissonant
dissonant : PI → Bool
dissonant (p , uni)  = false
dissonant (p , min2) = true
dissonant (p , maj2) = true
dissonant (p , min3) = false
dissonant (p , maj3) = false
dissonant (p , per4) = true
dissonant (p , aug4) = true
dissonant (p , per5) = false
dissonant (p , min6) = false
dissonant (p , maj6) = false
dissonant (p , min7) = true
dissonant (p , maj7) = true
dissonant (p , oct)  = false

-- Whether an interval is a fifth or octave
perfect58 : PI → Bool
perfect58 (p , uni)  = false
perfect58 (p , min2) = false
perfect58 (p , maj2) = false
perfect58 (p , min3) = false
perfect58 (p , maj3) = false
perfect58 (p , per4) = false
perfect58 (p , aug4) = false
perfect58 (p , per5) = true
perfect58 (p , min6) = false
perfect58 (p , maj6) = false
perfect58 (p , min7) = false
perfect58 (p , maj7) = false
perfect58 (p , oct)  = true

-- Whether an interval is an imperfect consonance
-- (i.e., the third or sixth)
imperfectc : PI → Bool
imperfectc (p , uni)  = false
imperfectc (p , min2) = false
imperfectc (p , maj2) = false
imperfectc (p , min3) = true
imperfectc (p , maj3) = true
imperfectc (p , per4) = false
imperfectc (p , aug4) = false
imperfectc (p , per5) = false
imperfectc (p , min6) = true
imperfectc (p , maj6) = true
imperfectc (p , min7) = false
imperfectc (p , maj7) = false
imperfectc (p , oct)  = false

-- Direction between two pitches
direction : Pitch → Pitch → Direction
direction p₁ p₂ with (pton p₂ ⊖ pton p₁)
... | pos (suc n) = upward
... | pos zero    = same
... | negsuc n    = downward

-- Whether two bars form a direct motion
-- (i.e., go in the same direction)
direct : PI → PI → Bool
direct pi₁ pi₂ with direction (proj₁ pi₁) (proj₁ pi₂)
                  | direction (cpitch pi₁) (cpitch pi₂)
... | upward   | upward   = true
... | upward   | same     = false
... | upward   | downward = false
... | same     | _        = false
... | downward | upward   = false
... | downward | same     = false
... | downward | downward = true

-- Whether two bars form direct fifth or octave
direct58 : PI → PI → Bool
direct58 pi₁ pi₂ with direct pi₁ pi₂ | perfect58 pi₂
... | true  | true  = true
... | true  | false = false
... | false | _     = false

-- Whether two bars form a contrary motion
contrary : PI → PI → Bool
contrary pi₁ pi₂ with direction (proj₁ pi₁) (proj₁ pi₂)
                    | direction (cpitch pi₁) (cpitch pi₂)
... | upward   | upward   = false
... | upward   | same     = false
... | upward   | downward = true
... | same     | _        = false
... | downward | upward   = true
... | downward | same     = false
... | downward | downward = false

-- Whether the counterpoint line repeats the same note
repeated : PI → PI → Bool
repeated pi₁ pi₂ with (pton (cpitch pi₂)) ⊖ (pton (cpitch pi₁))
... | pos zero    = true
... | pos (suc n) = false
... | negsuc n    = false

-- Conversion from booleans to natural numbers
bton : Bool → ℕ
bton true  = 1
bton false = 0

-- Type of refinements on a single bar
R₁ : Set
R₁ = List ((PI → Bool) × ℤ)

-- Type of refinements on two adjacent bars
R₂ : Set
R₂ = List ((PI → PI → Bool) × ℤ)

-- Sum of weights of satisfied predicates in R₁
weight₁ : R₁ → PI → ℤ
weight₁ r₁ pi =
  foldr (λ r a → (pos (bton ((proj₁ r) pi))) * (proj₂ r) +ℤ a) (pos 0) r₁

-- Sum of weights of satisfied predicates in R₂
weight₂ : R₂ → PI → PI → ℤ
weight₂ r₂ pi₁ pi₂ =
  foldr (λ r a → (pos (bton ((proj₁ r) pi₁ pi₂))) * (proj₂ r) +ℤ a) (pos 0) r₂

-- Type of first species counterpoint
data FS (r₁ : R₁) (r₂ : R₂) : ℤ → Set
-- Last bar of counterpoint
last : {r₁ : R₁} {r₂ : R₂} {z : ℤ} → FS r₁ r₂ z → PI

data FS r₁ r₂ where
  [_]   : (pi : PI) → FS r₁ r₂ (weight₁ r₁ pi)
  _++_  : {z : ℤ} →
          (cp : FS r₁ r₂ z) → (pi : PI) →
          FS r₁ r₂ (z +ℤ weight₁ r₁ pi +ℤ weight₂ r₂ (last cp) pi)

last [ pi ] = pi
last (cp ++ pi) = pi

infix 40 [_]
infixl 30 _++_

-- Define -∞ as -100 (since Agda does not have ∞ : ℕ)
-∞ : ℤ
-∞ = negsuc 99

-- Refinements on a single bar
-- (M1) Never use dissonant intervals
-- (N1) Use imperfect intervals as often as possible
-- (N3) Try to avoid chromatic notes
ψ₁ : R₁
ψ₁ = (dissonant , -∞) ∷ (imperfectc , pos 40) ∷ (chromatic , negsuc 39) ∷ []

-- Refinements on two adjacent bars
-- (M2) Never approach a fifth or an octave by direct motion
-- (N2) Use contrary motion as often as possible
-- (N4) Try to avoid repeated notes
ψ₂ : R₂
ψ₂ = (direct58 , -∞) ∷ (contrary , pos 50) ∷ (repeated , negsuc 29) ∷ []

-- Figure 1 left
fs1 : FS ψ₁ ψ₂ (pos 270)
fs1 = [ (c , oct) ] ++ (e , min3) ++ (f , maj3) ++ (d , maj6) ++ (c , oct)

{-
Rewards and penalties
bar1 = 0
bar2 = 40 (imperfect consonance)
bar3 = 40 (imperfect consonance)
bar4 = 40 (imperfect consonance)
bar5 = 0
bar1-bar2 = 50 (contrary motion)
bar2-bar3 = 0
bar3-bar4 = 50 (contrary motion)
bar4-bar5 = 50 (contrary motion)
-}

-- Figure 1 middle
fs2 : FS ψ₁ ψ₂ (negsuc 59)
fs2 = [ (c , oct) ] ++ (e , per4) ++ (f , per5) ++ (d , maj6) ++ (c , oct)

{-
Rewards and penalties
bar1 = 0
bar2 = -100 (dissonance)
bar3 = 0
bar4 = 40 (imperfect consonance)
bar5 = 0
bar1-bar2 = 50 (contrary motion)
bar2-bar3 = -100 (direct fifth)
bar3-bar4 = 0
bar4-bar5 = 50 (contrary motion)
-}

-- Figure 1 right
fs3 : FS ψ₁ ψ₂ (pos 230)
fs3 = [ (c , oct) ] ++ (e , min3) ++ (f , min3) ++ (d , maj6) ++ (c , oct)

{-
Rewards and penalties
bar1 = 0
bar2 = 40 (imperfect consonance)
bar3 = 40 (imperfect consonance) - 40 (chromatic note)
bar4 = 40 (imperfect consonance)
bar5 = 0
bar1-bar2 = 50 (contrary motion)
bar2-bar3 = 0
bar3-bar4 = 50 (contrary motion)
bar4-bar5 = 50 (contrary motion)
-}
