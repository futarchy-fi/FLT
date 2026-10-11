/-
Copyright (c) 2026 krandder. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: krandder
-/
module

public import FLT.Mazur.WeierstrassSmoothHorizontalConcreteAction

/-!
# Units needed for interior incidence transport

Both original conic residues lie in the input incidence open. Their actual
integral action outputs also lie in the output incidence open, with the two
independent residue parameters retained.
-/

@[expose] public noncomputable section
open IsLocalRing
open scoped LaurentPolynomial
namespace FLT.Mazur.WeierstrassIntegralChart
open WeierstrassModificationReesCoordinates
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
universe u
variable {R : Type u} [CommRing R] [IsDomain R] [IsLocalRing R]
  {W : WeierstrassCurve R} {π : R} {depth k : ℕ} (D : SplitNodeDepth W π depth)
  (d : WeierstrassDividedDepth.Data W π k) (hk0 : 0 < k) (hk : 2 * k < depth) (hπ : π ≠ 0)
local notation "K" => ResidueField R
local notation "C" => SmoothHorizontalResidueRing D
local notation "ψ" => smoothHorizontalInput W (π ^ k)
local notation "t" => horizontalScale W (π ^ k)
local notation "e₁" => smoothHorizontalFirstResidue D k hk0 hk hπ
  d.b3 d.b4 d.b6 d.factor3 d.factor4 d.factor6
local notation "e₂" => smoothHorizontalSecondResidue D k hk0 hk hπ
  d.b3 d.b4 d.b6 d.factor3 d.factor4 d.factor6
local notation "M" => smoothHorizontalActionLift d
local notation "E₁" => smoothHorizontalFirstOutputResidue D d hk0 hk hπ
local notation "E₂" => smoothHorizontalSecondOutputResidue D d hk0 hk hπ

omit [IsDomain R] in
/-- The signed tangent coefficient times the independent conic parameter is invertible. -/
theorem smoothHorizontalConic_incidence_unit :
    IsUnit (smoothHorizontalResidueConic D
      (LaurentPolynomial.C (residue R W.a₁) * LaurentPolynomial.T 1)) := by
  have h : IsUnit (LaurentPolynomial.C (residue R W.a₁)) := by
    have h' := (WeierstrassDilatation.residueTangentUnit D).isUnit.map
      (LaurentPolynomial.C : K →+* K[T;T⁻¹])
    simpa only [WeierstrassDilatation.residueTangentUnit_val] using h'
  exact (h.mul (LaurentPolynomial.isUnit_T 1)).map
    (smoothHorizontalResidueConic D).toRingHom

omit [IsDomain R] in
/-- The opposite branch has the same unit property with the original negative sign. -/
theorem smoothHorizontalConic_opposite_incidence_unit :
    IsUnit (smoothHorizontalResidueConic D
      (-LaurentPolynomial.C (residue R W.a₁) * LaurentPolynomial.T 1)) := by
  rw [neg_mul, map_neg]
  exact (smoothHorizontalConic_incidence_unit D).neg

/-- The first actual integral input residue factors through its incidence open. -/
theorem smoothHorizontalFirstResidue_incidence_unit : IsUnit (e₁ (ψ t)) := by
  rw [smoothHorizontalFirstResidue_scale]
  exact smoothHorizontalConic_incidence_unit D

/-- The opposite actual integral input residue factors through the same incidence open. -/
theorem smoothHorizontalSecondResidue_incidence_unit : IsUnit (e₂ (ψ t)) := by
  rw [smoothHorizontalSecondResidue_scale]
  exact smoothHorizontalConic_opposite_incidence_unit D

/-- The first actual action output has invertible original incidence. -/
theorem smoothHorizontalFirstOutputResidue_incidence_unit : IsUnit (E₁ (M t)) := by
  rw [(smoothHorizontalFirstOutputResidue_action D d hk0 hk hπ).1]
  exact (smoothHorizontalTangentUnit D).isUnit.mul
    (smoothHorizontalFirstResidue_incidence_unit D d hk0 hk hπ)

/-- The opposite actual action output also has invertible original incidence. -/
theorem smoothHorizontalSecondOutputResidue_incidence_unit : IsUnit (E₂ (M t)) := by
  rw [(smoothHorizontalSecondOutputResidue_action D d hk0 hk hπ).1]
  exact (smoothHorizontalTangentUnit D)⁻¹.isUnit.mul
    (smoothHorizontalSecondResidue_incidence_unit D d hk0 hk hπ)

end FLT.Mazur.WeierstrassIntegralChart
