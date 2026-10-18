/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.CyclicCharacteristicEvenNormalizedGenerator
public import FLT.Mazur.CyclicCharacteristicOddNormalizedGenerator

/-!
# Specified Cartier generators on both normalized characteristic charts

The two actual atlas subgroups carry their specified orbit generators. These
sections remain Cartier generators after every base change, including at
non-etale levels and over nonreduced test schemes.
-/

@[expose] public noncomputable section
open CategoryTheory AlgebraicGeometry MonoidalCategory MonObj
namespace FLT.Mazur.CyclicCharacteristicAtlas
open GeneralizedEllipticCurve GeneralizedEllipticCurve.FiniteSubgroup GroupSectionBaseChange
variable (n : ℕ) [NeZero n]

/-- The chosen orbit generator on either actual normalized chart. -/
def normalizedGenerator : (b : Bool) →
    𝟙_ (Over (normalizedLocus n b)) ⟶ (normalizedSubgroup n b).carrier
  | false => evenNormalizedGenerator n
  | true => oddNormalizedGenerator n

/-- Both actual normalized sections are Cartier generators of their full subgroup. -/
theorem normalizedGenerator_cartier (b : Bool) :
    (normalizedSubgroup n b).IsCartierGenerator (normalizedGenerator n b) := by
  cases b
  · exact evenNormalizedGenerator_cartier n
  · exact oddNormalizedGenerator_cartier n

/-- Arbitrary tests retain the chosen Cartier generator on the direct pulled atlas subgroup. -/
theorem normalizedGenerator_pull_cartier (b : Bool) {T : Scheme}
    (q : T ⟶ normalizedLocus n b) :
    ((normalizedSubgroup n b).baseChange q).IsCartierGenerator
      (pullSection q (normalizedGenerator n b)) :=
  (normalizedGenerator_cartier n b).baseChange (normalizedSubgroup n b) q

end FLT.Mazur.CyclicCharacteristicAtlas
