/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.OneGonAdicIndependentCommonStage

public import FLT.Mazur.ArithmeticOneGonCommonCoefficientIso

/-!
# Normal forms for independent stage curves

Both supplied smooth stages refine to the same literal coefficient subring.
Their full generalized curves compare by the proved arithmetic coefficient
isomorphisms and the equality of the actual smoothing parameters.
-/

@[expose] public noncomputable section
open CategoryTheory AlgebraicGeometry
namespace FLT.Mazur.OneGonAdicIndependentModel
open Approximation OneGonAdicCharacterTower OneGonSmoothing CharacterSchemeBaseChange
open ArithmeticOneGonGeneralizedCurve
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
variable {R : Type} [CommRing R] (I : Ideal R) [IsAdicComplete I R]
  (t : R) (ht : t ∈ I) (n : ℕ) [NeZero n] (s u : Set R)
  (i : (CoefficientStage (base I t ht n s))ᵒᵖ)
  (j : (CoefficientStage (base I t ht n u))ᵒᵖ)
  (hs : complementaryInverse I t ht ∈ s) (hu : complementaryInverse I t ht ∈ u)

/-- The stage diagram uses exactly the algebra structure of the literal inclusion. -/
theorem stageBaseMap_eq (k : (CoefficientStage (base I t ht n s))ᵒᵖ) :
    stageBaseMap I t ht n s k = baseMap (base I t ht n s) (stageBase I t ht n s k) := rfl

/-- Normalize the stage object before constructing large generalized-curve comparisons. -/
theorem stageCurve_eq (k : (CoefficientStage (base I t ht n s))ᵒᵖ)
    (h : complementaryInverse I t ht ∈ s) :
    stageCurve I t ht n s k h =
      (ArithmeticOneGonGeneralizedCurve.curve (parameter I t ht n s)
        (parameter_complementaryUnit I t ht n s h)).baseChange
          (baseMap (base I t ht n s) (stageBase I t ht n s k)) := by
  unfold stageCurve
  rw [stageBaseMap_eq]
  rfl

end FLT.Mazur.OneGonAdicIndependentModel
