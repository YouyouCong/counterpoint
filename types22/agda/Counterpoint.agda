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

-- All intervals must be cosonant
data IntervalError : Set where
  dissonant : Interval → IntervalError

checkInterval : PitchInterval → Maybe IntervalError
checkInterval (p , i) with isConsonant i
checkInterval (p , i) | false = just (dissonant i)
checkInterval (p , i) | true  = nothing

collectIntervalError : List PitchInterval → List IntervalError
collectIntervalError = mapMaybe checkInterval

------------------------------------------------

-- No direct fifth or octave is allowed
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

isDirect : PitchInterval → PitchInterval → Bool 
isDirect pi₁ pi₂ with motion pi₁ pi₂
isDirect pi₁ pi₂ | contrary = false
isDirect pi₁ pi₂ | oblique  = false
isDirect pi₁ pi₂ | parallel = true
isDirect pi₁ pi₂ | similar  = true

data MotionError : Set where
  direct58 : PitchInterval → PitchInterval → MotionError

checkMotion : PitchInterval → PitchInterval → Maybe MotionError
checkMotion pi₁ pi₂ with isDirect pi₁ pi₂ | isPerfect (proj₂ pi₂)
checkMotion pi₁ pi₂ | true  | true  = just (direct58 pi₁ pi₂)
checkMotion pi₁ pi₂ | _     | _     = nothing

collectMotionError : List PitchInterval → List MotionError
collectMotionError = mapMaybe (uncurry checkMotion) ∘ pairs

------------------------------------------------

-- Correct counterpoint
record CP : Set where
  constructor cp
  field
    bars       : List PitchInterval
    intervalOK : collectIntervalError bars ≡ []
    motionOK   : collectMotionError bars ≡ []

------------------------------------------------

-- First species counterpoint for Frog's Song (musical content)
bars-correct : List PitchInterval 
bars-correct = (c 5 , per8) ∷ (d 5 , maj6) ∷ (e 5 , min6) ∷ (f 5 , maj3) ∷ (e 5 , min3) ∷ (d 5 , maj6) ∷ (c 5 , per8) ∷ []

bars-dissonant : List PitchInterval 
bars-dissonant = (c 5 , per8) ∷ (d 5 , per8) ∷ (e 5 , per4) ∷ (f 5 , maj2) ∷ (e 5 , per4) ∷ (d 5 , maj6) ∷ (c 5 , per8) ∷ []

bars-direct58 : List PitchInterval
bars-direct58 = (c 5 , maj3) ∷ (d 5 , per5) ∷ (e 5 , min3) ∷ (f 5 , per5) ∷ (e 5 , per8) ∷ (d 5 , per8) ∷ (c 5 , per8) ∷ []

-- Beethoven's Pathetique Sonata (musical content)
bars-pathetique : List PitchInterval
bars-pathetique = (a♭ 4 , maj3) ∷ (d♭ 4 , maj10) ∷ (g 4 , min3) ∷ (c 4 , min10) ∷ (f 4 , min3) ∷ (b♭ 3 , min7) ∷ (b♭ 3 , min10) ∷ (c 4 , per8) ∷ (d♭ 4 , min6) ∷ (b 4 , aug4) ∷ (e♭ 4 , maj3) ∷ (e♭ 3 , maj10) ∷ []

-- Correct first species counterpoint
cp-correct : CP
cp-correct = cp bars-correct refl refl

-- Incorrect first species counterpoint
-- cp-dissonant : CP
-- cp-dissonant = cp bars-dissonant refl refl

-- cp-direct58 : CP
-- cp-direct58 = cp bars-direct58 refl refl

-- pathetique : CP
-- pathetique = cp bars-pathetique refl refl
