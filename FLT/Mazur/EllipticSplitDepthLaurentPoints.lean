/-
Copyright (c) 2026 krandder. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: krandder
-/
module

public import FLT.Mazur.EllipticSplitDepthResidueCharacter
public import FLT.Mazur.WeierstrassSplitNodalPointBaseChange
public import FLT.Mazur.WeierstrassInfinityResidueGeometry

/-!
# Laurent points of the actual original split residue cubic

Transport the existing nodal unit parametrization along the proved original
equation equality. Its classical character is the inverse Laurent unit,
including infinity, and every smooth residue point is recovered this way.
-/

@[expose] public noncomputable section
open AlgebraicGeometry CategoryTheory IsLocalRing WeierstrassCurve
namespace FLT.Mazur.WeierstrassIntegralChart
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
universe u

/-- Equal-equation transport commutes with passage to the classical affine point. -/
theorem projectivePointEquationCongr_toAffine {F : Type u} [Field F] [DecidableEq F]
    {U V : WeierstrassCurve F} (h : U = V) (P : U.toProjective.Point) :
    (projectivePointEquationCongr h P).toAffineLift =
      Affine.Point.equivOfEq h P.toAffineLift := by
  subst V
  rfl

variable {K : Type u} [Field K] {A : ValuationSubring K}
  {W : WeierstrassCurve A} {π : A} {depth : ℕ} (D : SplitNodeDepth W π depth)
local notation "F" => ResidueField A
local notation "a" => WeierstrassDilatation.residueTangentUnit D

/-- The unit Laurent point on the original residue equation. -/
def splitDepthLaurentPoint (t : Fˣ) : (W.map (residue A)).toProjective.Point :=
  projectivePointEquationCongr (splitDepth_residue_curve D).symm (splitNodalUnitPointEquiv a t)

/-- Original equation transport leaves the explicit homogeneous point unchanged. -/
theorem splitDepthLaurentPoint_point (t : Fˣ) :
    (splitDepthLaurentPoint D t).point = (splitNodalUnitPointEquiv a t).point :=
  projectivePointEquationCongr_point _ _

variable [DecidableEq (ResidueField A)]

/-- The original smooth residue character is inverse to the retained Laurent unit. -/
theorem splitDepthLaurentPoint_character (t : Fˣ) :
    Additive.toMul (splitDepthResidueCharacter D (splitDepthLaurentPoint D t).toAffineLift) =
      t⁻¹ := by
  have ht : Affine.Point.equivOfEq (splitDepth_residue_curve D)
      (splitDepthLaurentPoint D t).toAffineLift =
        (splitNodalUnitPointEquiv a t).toAffineLift := by
    rw [← projectivePointEquationCongr_toAffine, splitDepthLaurentPoint]
    have he : projectivePointEquationCongr (splitDepth_residue_curve D)
        (projectivePointEquationCongr (splitDepth_residue_curve D).symm
          (splitNodalUnitPointEquiv a t)) = splitNodalUnitPointEquiv a t := by
      apply Projective.Point.ext
      rw [projectivePointEquationCongr_point, projectivePointEquationCongr_point]
    rw [he]
  apply Units.ext
  change splitNodeParameter (residue A W.a₁)
    (Affine.Point.equivOfEq (splitDepth_residue_curve D)
      (splitDepthLaurentPoint D t).toAffineLift) = _
  rw [ht]
  convert splitNodalUnitPoint_classical_parameter a t using 1
  · congr 1
  · exact Units.val_inv_eq_inv_val t

/-- Every original smooth residue point has the inverse-character Laurent parameter. -/
theorem splitDepthLaurentPoint_inverse_character (P : (W.map (residue A)).toProjective.Point) :
    splitDepthLaurentPoint D (Additive.toMul (splitDepthResidueCharacter D P.toAffineLift))⁻¹ =
      P := by
  apply (Projective.Point.toAffineAddEquiv (W.map (residue A)).toProjective).injective
  apply (splitDepthResidueCharacter D).injective
  change Additive.ofMul (Additive.toMul
    (splitDepthResidueCharacter D (splitDepthLaurentPoint D _).toAffineLift)) = _
  rw [splitDepthLaurentPoint_character, inv_inv]
  rfl

end FLT.Mazur.WeierstrassIntegralChart
