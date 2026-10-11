/-
Copyright (c) 2026 krandder. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: krandder
-/
module

public import FLT.Mazur.WeierstrassInfinityResidueGeometry
public import FLT.Mazur.WeierstrassIntegralZeroSection

/-!
# The original infinity section in residue Laurent coordinates

Evaluation at Laurent parameter one preserves the original chart zero,
including its integral coefficient map.
-/

@[expose] public noncomputable section
open IsLocalRing AlgebraicGeometry CategoryTheory MonoidalCategory MonObj
open scoped LaurentPolynomial
namespace FLT.Mazur.WeierstrassIntegralChart
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
universe u
variable {R : Type u} [CommRing R] [IsDomain R] [IsLocalRing R]
  {W : WeierstrassCurve R} {π : R} {depth : ℕ} (D : SplitNodeDepth W π depth)
  (hdepth : 0 < depth)
local notation "K" => ResidueField R

/-- The Laurent identity evaluates every original coordinate at the original infinity point. -/
theorem infinityResidueOriginalMap_counit :
    ((Bialgebra.counitAlgHom K K[T;T⁻¹]).restrictScalars R).comp
      (infinityResidueOriginalMap D hdepth) = chartInfinityEvaluation W := by
  apply hom_ext
  intro i
  rw [AlgHom.comp_apply, infinityResidueOriginalMap_coord]
  fin_cases i <;> simp [chartInfinityEvaluation_coord, splitNodalLaurentX,
    splitNodalLaurentZ, Bialgebra.counitAlgHom, LaurentPolynomial.counit_T]

/-- The identity of the full residue infinity torus projects to the original integral zero. -/
@[reassoc] theorem infinityResidueIso_one_projection :
    η[MultiplicativeGroupScheme.gm K].left ≫ (infinityResidueIso D hdepth).hom ≫
        TensorOpenChart.projection =
      Spec.map (CommRingCat.ofHom (algebraMap R K)) ≫
        Spec.map (CommRingCat.ofHom (chartInfinityEvaluation (S := R) W).toRingHom) := by
  rw [infinityResidueIso_projection, one_spec_asOver_spec_left, ← Spec.map_comp,
    ← Spec.map_comp]
  congr 1
  apply CommRingCat.hom_ext
  change (((Bialgebra.counitAlgHom K K[T;T⁻¹]).restrictScalars R).comp
    (infinityResidueOriginalMap D hdepth)).toRingHom = _
  rw [infinityResidueOriginalMap_counit, chartInfinityEvaluation_base]
  rfl

/-- The original projective zero is the contraction of the Laurent identity. -/
@[reassoc] theorem infinityResidueContraction_one :
    η[MultiplicativeGroupScheme.gm K].left ≫ infinityResidueContraction D hdepth =
      Spec.map (CommRingCat.ofHom (algebraMap R K)) ≫ integralCurveZero W := by
  rw [← infinityResidueIso_contraction, infinityResidueIso_one_projection_assoc]
  rfl

end FLT.Mazur.WeierstrassIntegralChart
