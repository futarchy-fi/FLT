/-
Copyright (c) 2026 krandder. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: krandder
-/
module

public import FLT.Mazur.EllipticNodeComponentLabel
public import FLT.Mazur.EllipticSplitNodeGroup
public import FLT.Mathlib.AlgebraicGeometry.EllipticCurve.Affine.Point

/-!
# The multiplicative character of the original smooth residue cubic

The normalized coefficients identify the actual residue equation with its split
node. Its standard multiplicative parameter therefore gives an injective
character, and composition with actual reduction gives a homomorphism on E₀.
-/

@[expose] public noncomputable section
namespace FLT.Mazur
set_option backward.isDefEq.respectTransparency false
open IsLocalRing WeierstrassCurve
variable {K : Type*} [Field K] {A : ValuationSubring K} {W : WeierstrassCurve A}
  {π : A} {n : ℕ} (D : SplitNodeDepth W π n)

include D in
/-- The original reduced equation is the normalized split node. -/
theorem splitDepth_residue_curve : W.map (residue A) = splitNodeCurve (residue A W.a₁) := by
  have h3 := Ideal.pow_le_self (show n + 1 ≠ 0 by omega) D.a₃_mem
  have h4 := Ideal.pow_le_self (show n + 1 ≠ 0 by omega) D.a₄_mem
  have h6 := Ideal.pow_le_self (Nat.ne_of_gt D.depth_pos) D.a₆_mem
  ext <;> simp [splitNodeCurve, (residue_eq_zero_iff _).mpr D.a₂_mem,
    (residue_eq_zero_iff _).mpr h3, (residue_eq_zero_iff _).mpr h4,
    (residue_eq_zero_iff _).mpr h6]

variable [DecidableEq (ResidueField A)]

/-- The actual smooth residue cubic, identified with the multiplicative group. -/
def splitDepthResidueCharacter :
    (W.map (residue A)).toAffine.Point ≃+ Additive (ResidueField A)ˣ :=
  (Affine.Point.equivOfEq (splitDepth_residue_curve D)).trans
    (splitNodeParameterAddEquiv ((residue_ne_zero_iff_isUnit _).mpr D.a₁_unit))

/-- On the affine chart the original character is the quotient of tangent slopes. -/
theorem splitDepthResidueCharacter_some (x y : ResidueField A)
    (h : (W.map (residue A)).toAffine.Nonsingular x y) :
    (Additive.toMul (splitDepthResidueCharacter D (.some x y h))).val =
      (y / x) / (y / x + residue A W.a₁) := by
  simp only [splitDepthResidueCharacter, AddEquiv.trans_apply, Affine.Point.equivOfEq_some,
    splitNodeParameterAddEquiv, AddEquiv.ofBijective_apply, splitNodeParameterHom,
    AddMonoidHom.coe_mk, ZeroHom.coe_mk, splitNodeParameterUnit,
    splitNodeParameter]
  rfl

/-- The character equals one exactly at the point at infinity. -/
theorem splitDepthResidueCharacter_eq_one_iff (p : (W.map (residue A)).toAffine.Point) :
    Additive.toMul (splitDepthResidueCharacter D p) = 1 ↔ p = 0 := by
  change splitDepthResidueCharacter D p = 0 ↔ p = 0
  exact map_eq_zero_iff (splitDepthResidueCharacter D) (splitDepthResidueCharacter D).injective

/-- Actual smooth reduction followed by the original nodal character. -/
def splitDepthSmoothCharacter : ellipticE0 A W →+ Additive (ResidueField A)ˣ :=
  (splitDepthResidueCharacter D).toAddMonoidHom.comp
    ((Projective.Point.toAffineAddEquiv (W.map (residue A)).toProjective).toAddMonoidHom.comp
      (smoothReductionHom A W))

/-- A relation to an actual smooth residue point computes the character on E₀. -/
theorem splitDepthSmoothCharacter_of_reducesTo
    (P : (W.map (algebraMap A K)).toAffine.Point)
    (p : (W.map (residue A)).toAffine.Point) (h : ReducesTo A W P p)
    (hs : SmoothReduction A W P.toProjective) :
    splitDepthSmoothCharacter D ⟨P.toProjective, hs⟩ = splitDepthResidueCharacter D p := by
  change splitDepthResidueCharacter D
    ((Projective.Point.toAffineAddEquiv (W.map (residue A)).toProjective)
      (smoothReductionHom A W ⟨P.toProjective, hs⟩)) = _
  apply congrArg (splitDepthResidueCharacter D)
  apply (Projective.Point.toAffineAddEquiv (W.map (residue A)).toProjective).symm.injective
  rw [AddEquiv.symm_apply_apply]
  exact Projective.Point.ext h

/-- Equality of characters is equality of the actual smooth reductions. -/
theorem splitDepthSmoothCharacter_eq_iff (P Q : ellipticE0 A W) :
    splitDepthSmoothCharacter D P = splitDepthSmoothCharacter D Q ↔
      smoothReductionHom A W P = smoothReductionHom A W Q := by
  change splitDepthResidueCharacter D
    ((Projective.Point.toAffineAddEquiv (W.map (residue A)).toProjective)
      (smoothReductionHom A W P)) = splitDepthResidueCharacter D
      ((Projective.Point.toAffineAddEquiv (W.map (residue A)).toProjective)
        (smoothReductionHom A W Q)) ↔ _
  rw [(splitDepthResidueCharacter D).injective.eq_iff]
  exact (Projective.Point.toAffineAddEquiv
    (W.map (residue A)).toProjective).injective.eq_iff

end FLT.Mazur
