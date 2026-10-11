/-
Copyright (c) 2026 krandder. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: krandder
-/
module

public import FLT.Mazur.WeierstrassFractionSmoothPresentationLift
public import FLT.Mazur.WeierstrassGlobalModificationGluing
public import FLT.Mazur.WeierstrassModificationReesProjIso

/-!
# Actual affine-output action lifts into the whole original modification

Transport the constructed Rees lift through the actual modification-Proj
isomorphism, then include the local modification in the complete projective
model. The original cubic action is retained exactly. The divided coefficient
convention is handled explicitly by replacing b6 with s*b6 in the center lift.
-/

@[expose] public noncomputable section

open AlgebraicGeometry CategoryTheory

namespace FLT.Mazur.WeierstrassIntegralChart

set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true

universe u
variable {R : Type u} [CommRing R] [IsDomain R] [IsBezout R]
  (W : WeierstrassCurve R) (s b3 b4 b6 : R)
  (h3 : W.a₃ = s * b3) (h4 : W.a₄ = s * b4) (h6 : W.a₆ = s ^ 2 * b6) (hs : s ≠ 0)
  (f : Coordinate W 2) (hf : f ∈ modificationChartCenter W s 2)
  (i : (fractionSmoothCover W s f).I₀)
  (hi : modifiedSmoothOutputIndex W (fractionSmoothContraction W s f) i = 2)

/-- The constructed local action into the whole original projective modification. -/
irreducible_def fractionSmoothPresentationToGlobal :
    Spec ((fractionSmoothCover W s f).X i) ⟶
      WeierstrassGlobalModification.model W s b3 b4 b6 h3 h4 h6 hs :=
  fractionSmoothPresentationToRees W s b3 b4 (s * b6) h3 h4
    (by simpa only [pow_two, mul_assoc] using h6) f hf i hi ≫
      (WeierstrassModificationReesCoordinates.modificationProjIso
        W s b3 b4 b6 h3 h4 h6 hs).inv ≫
          WeierstrassGlobalModification.localChart W s b3 b4 b6 h3 h4 h6 hs

/-- The local lifted action contracts to the actual whole-input action on this source member. -/
@[reassoc] theorem fractionSmoothPresentationToGlobal_action :
    fractionSmoothPresentationToGlobal W s b3 b4 b6 h3 h4 h6 hs f hf i hi ≫
        WeierstrassGlobalModification.contraction W s b3 b4 b6 h3 h4 h6 hs =
      (fractionSmoothCover W s f).f i ≫
        modifiedSmoothAffineAddition W (fractionSmoothContraction W s f) := by
  rw [fractionSmoothPresentationToGlobal_def, Category.assoc, Category.assoc,
    WeierstrassGlobalModification.localChart_contraction,
    WeierstrassModificationReesCoordinates.modificationProjIso_inv_contraction]
  exact fractionSmoothPresentationToRees_action W s b3 b4 (s * b6) h3 h4
    (by simpa only [pow_two, mul_assoc] using h6) f hf i hi

/-- The local lifted action also retains the original smooth parameter's coefficient map. -/
@[reassoc] theorem fractionSmoothPresentationToGlobal_structure :
    fractionSmoothPresentationToGlobal W s b3 b4 b6 h3 h4 h6 hs f hf i hi ≫
        WeierstrassGlobalModification.contraction W s b3 b4 b6 h3 h4 h6 hs ≫
          integralCurveStructure W =
      modifiedSmoothAffineParameter W (fractionSmoothContraction W s f) i ≫
        integralSmoothStructure W := by
  rw [fractionSmoothPresentationToGlobal_action_assoc, ← Category.assoc,
    modifiedSmoothAffineCover_addition,
    leftSmoothPointAddition_structure]

end FLT.Mazur.WeierstrassIntegralChart
