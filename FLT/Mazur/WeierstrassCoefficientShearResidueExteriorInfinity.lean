/-
Copyright (c) 2026 krandder. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: krandder
-/
module

public import FLT.Mazur.WeierstrassResidueInfinityTensorParameter
public import FLT.Mazur.WeierstrassCoefficientShearResidueExteriorLift

/-!
# The actual exterior contains the full original infinity chart

The complete residue infinity parameter lifts through the unchanged infinity
pullback. Both coefficient projections identify its map into the actual atlas.
-/

@[expose] public noncomputable section
open AlgebraicGeometry CategoryTheory Limits IsLocalRing
open scoped TensorProduct
namespace FLT.Mazur.WeierstrassDividedDepth
open WeierstrassIntegralChart ProjectiveLine
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
set_option quotPrecheck false
variable {R : Type} [CommRing R] [IsDomain R] [IsBezout R] [IsLocalRing R]
  {W : WeierstrassCurve R} {π : R} (hπ : π ≠ 0) {start n : ℕ}
  (data : (i : Fin (n + 1)) → Data W π (start + i.val)) (j : ℕ) (hj : j ≤ n)
  {k : ℕ} (d : Data W π k) (hk : 0 < k) (hres : residue R π = 0)
local notation "V" => W.map (residue R)
local notation "Q" => AdjoinRoot (nodeTangentPolynomial V)
local notation "r" => AdjoinRoot.root (nodeTangentPolynomial V)
variable [Fact (Irreducible (nodeTangentPolynomial (W.map (residue R))))]
  (a : (AdjoinRoot (nodeTangentPolynomial (W.map (residue R))))ˣ)
  (ha : (a : AdjoinRoot (nodeTangentPolynomial (W.map (residue R)))) =
    (nodeTangentShear (W.map (residue R))).a₁)
local notation "P" => residueInfinityTensorParameter d hk hres a ha
local notation "N" => originalResidueFiniteNormalization hπ data j hj d hk hres
local notation "F" => coefficientShearResidueExteriorLift hπ data j hj d hk hres a
local notation "s" => coefficientShearGluedStructure hπ data Q r j hj
local notation "p" => coefficientShearGluedProjection hπ data Q r j hj
local notation "I" => coefficientShearGluedChart hπ data Q r j hj (.inl 0)

/-- The full infinity parameter retains its actual lift through every finite modification. -/
@[reassoc] theorem residueInfinityTensorParameter_finite :
    P ≫ N = TensorOpenChart.projection ≫ finiteInfinityChart hπ data j hj := by
  let H := finiteInfinity_isPullback hπ data j hj
  have hw : TensorOpenChart.projection ≫ integralCurveChart W 1 =
      (P ≫ N) ≫ finiteGlobalContraction hπ data j hj := by
    rw [Category.assoc, originalResidueFiniteNormalization_contraction,
      residueInfinityTensorParameter_normalization]
  have h₁ := H.lift_fst TensorOpenChart.projection (P ≫ N) hw
  have h₂ := H.lift_snd TensorOpenChart.projection (P ≫ N) hw
  have hl : H.lift TensorOpenChart.projection (P ≫ N) hw = TensorOpenChart.projection := by
    simpa only [Category.comp_id] using h₁
  rw [hl] at h₂
  exact h₂.symm

/-- The ordered complete exterior contains the entire original infinity chart of the model. -/
@[reassoc] theorem coefficientShearResidueExteriorLift_infinityChart :
    P ≫ (slopeNormalizationIso a).hom ≫ F = I := by
  apply (coefficientShearGlued_isPullback hπ data Q r j hj).hom_ext
  · simp only [Category.assoc]
    rw [coefficientShearResidueExteriorLift_structure, slopeNormalizationIso_base,
      residueInfinityTensorParameter_structure, coefficientShearGluedChart_structure]
    rfl
  · simp only [Category.assoc]
    rw [coefficientShearResidueExteriorLift_projection,
      coefficientShearResidueOrderedFinite, Iso.hom_inv_id_assoc,
      residueInfinityTensorParameter_finite, coefficientShearGluedChart_projection]
    change TensorOpenChart.projection ≫ finiteInfinityChart hπ data j hj =
      finiteInfinityTensorChart hπ data Q j hj ≫ pullback.snd _ _
    exact (TensorOpenChart.chart_snd _ _ _).symm

include ha in
/-- Agreement on the complete exterior implies agreement on the full original infinity chart. -/
theorem coefficientShearResidueInfinityChart_hom_ext {Y : Scheme}
    (u v : coefficientShearGlued hπ data Q r j hj ⟶ Y) (hF : F ≫ u = F ≫ v) :
    I ≫ u = I ≫ v := by
  rw [← coefficientShearResidueExteriorLift_infinityChart
    hπ data j hj d hk hres a ha]
  simpa only [Category.assoc] using
    congrArg (fun f => P ≫ (slopeNormalizationIso a).hom ≫ f) hF

end FLT.Mazur.WeierstrassDividedDepth
