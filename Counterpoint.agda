-- First species counterpoint
module Counterpoint where

open import Data.Bool using (Bool; true; false; if_then_else_; _∨_; _∧_; not)
open import Data.Fin using (Fin; #_)
open import Data.Integer using (+_)
open import Data.List using (List; []; _∷_; mapMaybe; map; zip; _++_; concatMap)
open import Data.Maybe using (Maybe; just; nothing)
open import Data.Nat using (suc; _+_; _≡ᵇ_; _<ᵇ_; compare; _∸_; ℕ; zero)
open import Data.Product using (_×_; _,_; proj₁; proj₂; uncurry)
open import Data.Vec using ([]; _∷_; Vec; lookup; drop; reverse)

open import Function using (_∘_)

open import Relation.Binary.PropositionalEquality using (_≡_; refl)

open import Music
open import Note
open import Pitch
open import Interval
open import Util using (pairs)

------------------------------------------------

-- First species

-- Beginning must be the 1st, 5th, or 8th
data BeginningError : Set where
  not158   : PitchInterval → BeginningError

checkBeginning : PitchInterval → Maybe BeginningError
checkBeginning pi@(_ , i) =
  if ((i == per1) ∨ (i == per5) ∨ (i == per8))
  then nothing
  else just (not158 pi)
  
------------------------------------------------

-- Intervals in middle bars must be consonant and non-unison
data IntervalError : Set where
  dissonant : Interval → IntervalError  -- 不協和音
  unison    : Pitch    → IntervalError  -- 1度の和音

intervalCheck : PitchInterval → Maybe IntervalError
intervalCheck (p , i) with isConsonant i | isUnison i
intervalCheck (p , i) | false | _    = just (dissonant i)
intervalCheck (p , i) | true | true  = just (unison p)
intervalCheck (p , i) | true | false = nothing

checkIntervals : List PitchInterval → List IntervalError
checkIntervals = mapMaybe intervalCheck

------------------------------------------------

-- Perfect intervals must not approached by parallel or similar motion
data Motion : Set where
  contrary : Motion
  parallel : Motion
  similar  : Motion
  oblique  : Motion

motion : PitchInterval → PitchInterval → Motion
motion (pitch p , interval i) (pitch q , interval j) =
  let p' = p + i; q' = q + j
  in if i ≡ᵇ j then parallel
     else (if (p ≡ᵇ q) ∨ (p' ≡ᵇ q') then oblique
           else (if p <ᵇ q then (if p' <ᵇ q' then similar  else contrary)
                 else           (if p' <ᵇ q' then contrary else similar)))

data MotionError : Set where
  parallel : PitchInterval → PitchInterval → MotionError
  similar  : PitchInterval → PitchInterval → MotionError

motionCheck : PitchInterval → PitchInterval → Maybe MotionError
motionCheck i1 i2 with motion i1 i2 | isPerfect (proj₂ i2)
motionCheck i1 i2 | contrary | _     = nothing
motionCheck i1 i2 | oblique  | _     = nothing
motionCheck i1 i2 | parallel | false = nothing
motionCheck i1 i2 | parallel | true  = just (parallel i1 i2)
motionCheck i1 i2 | similar  | false = nothing
motionCheck i1 i2 | similar  | true  = just (similar i1 i2)

checkMotion : List PitchInterval → List MotionError
checkMotion = mapMaybe (uncurry motionCheck) ∘ pairs

------------------------------------------------

-- Ending must be the 1st or 8th approached by a cadence
data EndingError : Set where
  not18    : PitchInterval → EndingError
  not27    : PitchInterval → EndingError
  tooShort : List PitchInterval → EndingError

endingCheck : PitchInterval → PitchInterval → Maybe EndingError
endingCheck pi1@(pitch p , i) (pitch q , interval 0)  = 
  if ((p + 1 ≡ᵇ q) ∧ (i == min3)) then nothing else just (not27 pi1)
endingCheck pi1@(pitch p , i) (pitch q , interval 12) =
  if ((q + 2 ≡ᵇ p) ∧ (i == maj6) ∨ (p + 1 ≡ᵇ q) ∧ (i == min10))
  then nothing
  else just (not27 pi1)
endingCheck pi1               pi2                     =
  just (not18 pi2)

checkEnding : List PitchInterval → PitchInterval → Maybe EndingError
checkEnding []       _ = just (tooShort [])
checkEnding (p ∷ []) q = endingCheck p q
checkEnding (p₁ ∷ p₂ ∷ ps) q = checkEnding (p₂ ∷ ps) q

------------------------------------------------

-- Correct first species counterpoint
record FirstSpecies : Set where
  constructor firstSpecies
  field
    firstBar    : PitchInterval
    middleBars  : List PitchInterval
    lastBar     : PitchInterval
    beginningOk : checkBeginning firstBar ≡ nothing
    intervalsOk : checkIntervals middleBars ≡ []
    motionOk    : checkMotion (firstBar ∷ middleBars) ≡ []
    endingOk    : checkEnding middleBars lastBar ≡ nothing

------------------------------------------------

-- First species counterpoint for Frog's Song (musical content)
first : PitchInterval
first = (c 5 , per8)

first' : PitchInterval
first' = (c 5 , maj6)

middle : List PitchInterval 
middle = (d 5 , maj6) ∷ (e 5 , min6) ∷ (f 5 , maj3) ∷ (e 5 , min3) ∷ (d 5 , maj6) ∷ []

middle' : List PitchInterval 
middle' = (d 5 , per8) ∷ (e 5 , per4) ∷ (f 5 , per5) ∷ (e 5 , per5) ∷ (d 5 , per4) ∷ []

last : PitchInterval
last = (c 5 , per8)

last' : PitchInterval
last' = (c 5 , maj6)

-- Correct first species counterpoint
fs : FirstSpecies
fs = firstSpecies first middle last refl refl refl refl

-- Incorrect first species counterpoint
-- fs' : FirstSpecies
-- fs' = firstSpecies first' middle' last' refl refl refl refl
