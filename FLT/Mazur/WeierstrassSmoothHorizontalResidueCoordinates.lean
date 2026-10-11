/-
Copyright (c) 2026 krandder. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: krandder
-/
module

public import FLT.Mazur.WeierstrassSmoothHorizontalConcreteRefinement

/-!
# Named coordinates on the concrete conic and smooth residue product

The smooth Laurent parameter gives an actual unit on the common residue
source. The retained original fraction scale has the signed conic coordinate,
and the original normalized Y coordinates keep their independent smooth values.
-/

@[expose] public noncomputable section
open IsLocalRing
open scoped LaurentPolynomial
namespace FLT.Mazur.WeierstrassIntegralChart
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
universe u
variable {R : Type u} [CommRing R] [IsDomain R] [IsLocalRing R]
  {W : WeierstrassCurve R} {π : R} {depth k : ℕ} (D : SplitNodeDepth W π depth)
  (d : WeierstrassDividedDepth.Data W π k) (hk0 : 0 < k) (hk : 2 * k < depth) (hπ : π ≠ 0)
local notation "K" => ResidueField R
local notation "L" => K[T;T⁻¹]
local notation "P" => SmoothYParameterRing D
local notation "C" => SmoothHorizontalResidueRing D
local notation "S" => SmoothHorizontalProductRing W (π ^ k)
local notation "a" => WeierstrassDilatation.residueTangentUnit D
local notation "e₁" => smoothHorizontalFirstResidue D k hk0 hk hπ
  d.b3 d.b4 d.b6 d.factor3 d.factor4 d.factor6
local notation "e₂" => smoothHorizontalSecondResidue D k hk0 hk hπ
  d.b3 d.b4 d.b6 d.factor3 d.factor4 d.factor6
local notation "ψ" => smoothHorizontalInput W (π ^ k)
local notation "j" => smoothHorizontalResidueParameter D
open WeierstrassModificationReesCoordinates WeierstrassModificationX

/-- The named smooth Laurent coordinate is a unit on the actual residue product. -/
def smoothHorizontalTangentUnit : Cˣ :=
  ((LaurentPolynomial.isUnit_T (R := K) 1).map
    ((j).toRingHom.comp (algebraMap L P))).unit

omit [IsDomain R] in
/-- The constructed unit has exactly the positive smooth Laurent coordinate. -/
theorem smoothHorizontalTangentUnit_val :
    (smoothHorizontalTangentUnit D : C) = j (algebraMap L P (LaurentPolynomial.T 1)) :=
  IsUnit.unit_spec _

/-- The original scale on the first branch is a times the conic parameter. -/
theorem smoothHorizontalFirstResidue_scale :
    e₁ (ψ (horizontalScale W (π ^ k))) = smoothHorizontalResidueConic D
      (LaurentPolynomial.C (residue R W.a₁) * LaurentPolynomial.T 1) := by
  rw [smoothHorizontalFirstResidue_input]
  exact congrArg (smoothHorizontalResidueConic D)
    (horizontalConicFirstResidue_scale D k hk0 hk hπ
      d.b3 d.b4 d.b6 d.factor3 d.factor4 d.factor6)

/-- The original scale on the opposite branch retains the negative tangent sign. -/
theorem smoothHorizontalSecondResidue_scale :
    e₂ (ψ (horizontalScale W (π ^ k))) = smoothHorizontalResidueConic D
      (-LaurentPolynomial.C (residue R W.a₁) * LaurentPolynomial.T 1) := by
  rw [smoothHorizontalSecondResidue_input]
  exact congrArg (smoothHorizontalResidueConic D)
    (horizontalConicSecondResidue_scale D k hk0 hk hπ
      d.b3 d.b4 d.b6 d.factor3 d.factor4 d.factor6)

/-- The first conic branch leaves every smooth Y-chart function on the smooth factor. -/
theorem smoothHorizontalFirstResidue_y (q : Coordinate W 1) :
    e₁ (smoothHorizontalY W (π ^ k) q) =
      j (algebraMap L P (smoothYParameterResidue D (by omega) q)) := by
  change e₁ (smoothHorizontalParameter W (π ^ k) (smoothYAffineY W q)) = _
  rw [smoothHorizontalFirstResidue_parameter, smoothYAffineResidue_base]

/-- The opposite conic branch has the same independent smooth Y-chart functions. -/
theorem smoothHorizontalSecondResidue_y (q : Coordinate W 1) :
    e₂ (smoothHorizontalY W (π ^ k) q) =
      j (algebraMap L P (smoothYParameterResidue D (by omega) q)) := by
  change e₂ (smoothHorizontalParameter W (π ^ k) (smoothYAffineY W q)) = _
  rw [smoothHorizontalSecondResidue_parameter, smoothYAffineResidue_base]

omit [IsDomain R] in
/-- All coefficient maps on the smooth residue factor are the original base map. -/
theorem smoothHorizontalResidue_coefficient (q : R) :
    j (algebraMap L P (algebraMap K L (residue R q))) = algebraMap R C q := by
  rw [← IsScalarTower.algebraMap_apply K L P, AlgHom.commutes,
    IsScalarTower.algebraMap_apply R K C, ResidueField.algebraMap_eq]

/-- The named unit is the normalized tangent factor of the actual first smooth input. -/
theorem smoothHorizontalFirstResidue_tangent :
    (smoothHorizontalTangentUnit D : C) =
      1 + e₁ (algebraMap R S W.a₁) * e₁ (smoothHorizontalY W (π ^ k) (coord W 1 0)) := by
  rw [smoothHorizontalTangentUnit_val, AlgHom.commutes, smoothHorizontalFirstResidue_y,
    smoothYParameterResidue_coord]
  have h := congrArg (fun z : L => j (algebraMap L P z)) (splitNodalLaurent_tangent a)
  simp only [map_add, map_one, map_mul] at h
  rw [WeierstrassDilatation.residueTangentUnit_val, smoothHorizontalResidue_coefficient] at h
  exact h.symm

/-- The opposite branch uses precisely the same normalized smooth tangent unit. -/
theorem smoothHorizontalSecondResidue_tangent :
    (smoothHorizontalTangentUnit D : C) =
      1 + e₂ (algebraMap R S W.a₁) * e₂ (smoothHorizontalY W (π ^ k) (coord W 1 0)) := by
  rw [smoothHorizontalTangentUnit_val, AlgHom.commutes, smoothHorizontalSecondResidue_y,
    smoothYParameterResidue_coord]
  have h := congrArg (fun z : L => j (algebraMap L P z)) (splitNodalLaurent_tangent a)
  simp only [map_add, map_one, map_mul] at h
  rw [WeierstrassDilatation.residueTangentUnit_val, smoothHorizontalResidue_coefficient] at h
  exact h.symm

end FLT.Mazur.WeierstrassIntegralChart
