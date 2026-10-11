/-
Copyright (c) 2026 krandder. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: krandder
-/
module

public import FLT.Mazur.WeierstrassDividedPositiveEqualityCyclicTorusAction
public import FLT.Mazur.WeierstrassSmoothYAffineResidue

/-!
# The actual smooth affine parameter in the cyclic orientation

The cyclic coordinate is the inverse of the named smooth Laurent parameter.
This follows from the original smooth group isomorphism, and retains its
contraction to the original integral cubic.
-/

@[expose] public noncomputable section
open AlgebraicGeometry CategoryTheory IsLocalRing
open scoped LaurentPolynomial
namespace FLT.Mazur.WeierstrassDividedDepth
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
universe u
variable {R : Type u} [CommRing R] [IsDomain R] [IsLocalRing R]
  {W : WeierstrassCurve R} {π : R} {depth start : ℕ} (D : SplitNodeDepth W π depth)
  (s : ℕ) (hk : 2 * (start + s + 1) ≤ depth)
open WeierstrassIntegralChart
local notation "K" => ResidueField R
local notation "L" => K[T;T⁻¹]
local notation "P" => SmoothYParameterRing D
local notation "V" => W.map (algebraMap R K)
local notation "hd" => lt_of_lt_of_le (Nat.mul_pos (by decide) (Nat.succ_pos _)) hk
local notation "v" => positiveEqualityCyclicSmoothGroupIso D s hk
local notation "q" => Spec.map (CommRingCat.ofHom (algebraMap L P))

/-- The cyclic group isomorphism cancels the original reciprocal parameter map. -/
theorem positiveEqualityCyclicSmoothGroupIso_parameter :
    (ProjectiveLine.inversion K).hom ≫ (v).hom.hom.hom.hom.left =
      (infinityResidueSmoothIso D hd).hom := by
  rw [← PolygonSplitGroup.reciprocalGroupIso_left]
  change ((PolygonSplitGroup.reciprocalGroupIso K).hom ≫
    (positiveEqualityCyclicSmoothGroupIso D s hk).hom).hom.hom.hom.left = _
  simp only [positiveEqualityCyclicSmoothGroupIso, Iso.trans_hom, Iso.symm_hom,
    Iso.hom_inv_id_assoc]
  exact infinityResidueSmoothGroupIso_inv D hd

/-- The original affine smooth parameter mapped to the cyclic torus. -/
def smoothYParameterCyclicMap : Spec (.of P) ⟶ Spec (.of L) :=
  q ≫ (ProjectiveLine.inversion K).hom

/-- The cyclic parameter is attached to the actual original smooth point. -/
theorem smoothYParameterCyclicMap_original :
    smoothYParameterCyclicMap D ≫ (v).hom.hom.hom.hom.left =
      q ≫ (infinityResidueSmoothIso D hd).hom := by
  rw [smoothYParameterCyclicMap, Category.assoc,
    positiveEqualityCyclicSmoothGroupIso_parameter]

/-- Every original integral cubic function is retained by the cyclic parametrization. -/
theorem smoothYParameterCyclicMap_contraction :
    smoothYParameterCyclicMap D ≫ (v).hom.hom.hom.hom.left ≫
        (integralSmoothOpen V).ι ≫ integralCoefficientMorphism W =
      q ≫ infinityResidueContraction D hd := by
  rw [← Category.assoc, smoothYParameterCyclicMap_original, Category.assoc,
    infinityResidueSmoothIso_contraction]

/-- The full Laurent map underlying the cyclic coordinate, including negative powers. -/
def smoothYParameterCyclicAlgebra : L →ₐ[K] P :=
  (IsScalarTower.toAlgHom K L P).comp LaurentPolynomial.invert.toAlgHom

omit [IsDomain R] in
/-- Its spectrum is the actual cyclic parameter map. -/
theorem smoothYParameterCyclicAlgebra_spec :
    Spec.map (CommRingCat.ofHom (smoothYParameterCyclicAlgebra D).toRingHom) =
      smoothYParameterCyclicMap D := by
  rw [smoothYParameterCyclicAlgebra, smoothYParameterCyclicMap,
    ProjectiveLine.inversion_hom, ← Spec.map_comp]
  rfl

omit [IsDomain R] in
/-- The positive cyclic generator is the inverse named smooth generator. -/
theorem smoothYParameterCyclicAlgebra_T (i : ℤ) :
    smoothYParameterCyclicAlgebra D (LaurentPolynomial.T i) =
      algebraMap L P (LaurentPolynomial.T (-i)) := by
  change algebraMap L P (LaurentPolynomial.invert (LaurentPolynomial.T i)) = _
  rw [LaurentPolynomial.invert_T]

end FLT.Mazur.WeierstrassDividedDepth
