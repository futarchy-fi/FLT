/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.CyclicCharacteristicEvenNormalizedAuxiliary
public import FLT.Mazur.CyclicCharacteristicOddNormalizedAuxiliary

/-!
# Auxiliary labels on both normalized characteristic charts

Use the actual order-four frame on the even chart and the actual order-three
frame on the odd chart. This common interface allows local original frames
to assemble into one characteristic cover without forgetting their labels.
-/

@[expose] public noncomputable section
open CategoryTheory AlgebraicGeometry MonoidalCategory
namespace FLT.Mazur.CyclicCharacteristicAtlas
open UniversalWeierstrass (Labels labels_pow)

/-- The auxiliary order selected by the characteristic chart. -/
def normalizedAuxiliaryOrder : Bool → ℕ
  | false => 4
  | true => 3

/-- Both auxiliary label groups have their stated finite exponent. -/
theorem normalizedAuxiliaryLabels_pow (b : Bool) (i : Labels (normalizedAuxiliaryOrder b)) :
    i ^ normalizedAuxiliaryOrder b = 1 :=
  labels_pow (normalizedAuxiliaryOrder b) i

variable (n : ℕ) [NeZero n]

/-- The independent universal auxiliary sections on either actual normalized chart. -/
def normalizedAuxiliaryMarking : (b : Bool) → Labels (normalizedAuxiliaryOrder b) →
    (𝟙_ (Over (normalizedLocus n b)) ⟶ (normalizedCurve n b).group)
  | false => evenNormalizedAuxiliaryMarking n
  | true => oddNormalizedAuxiliaryMarking n

end FLT.Mazur.CyclicCharacteristicAtlas
