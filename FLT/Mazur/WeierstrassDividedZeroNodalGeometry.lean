/-
Copyright (c) 2026 krandder. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: krandder
-/
module

public import FLT.Mazur.WeierstrassDividedZeroNodalProjective
public import FLT.Mazur.WeierstrassNodalResidueContraction
public import FLT.Mazur.WeierstrassDividedInfinityLaurentChart

/-!
# Coefficients, original contraction and Laurent chart of the nodal projective comparison

The whole zero-stage isomorphism is over the actual residue field, contracts
to the original integral cubic, and retains the ordered infinity torus.
-/

@[expose] public noncomputable section
open AlgebraicGeometry CategoryTheory Limits IsLocalRing
namespace FLT.Mazur.WeierstrassDividedDepth
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
universe u
variable {R : Type u} [CommRing R] [IsDomain R] [IsBezout R] [IsLocalRing R]
  {W : WeierstrassCurve R} {π : R} (hπ : π ≠ 0) {start n depth : ℕ}
  (data : (i : Fin (n + 1)) → Data W π (start + i.val))
  (D : SplitNodeDepth W π depth) (hdepth : 0 < depth)
  (j : ℕ) (hj : j ≤ n) (hzero : start + j = 0)
open WeierstrassIntegralChart WeierstrassDilatation
local notation "K" => ResidueField R
local notation "a" => residueTangentUnit D
local notation "N" => splitNodalEquation a
local notation "e" => zeroNodalProjectiveIso hπ data D hdepth j hj hzero
local notation "q" => Spec.map (CommRingCat.ofHom (algebraMap R K))

/-- The whole nodal projective comparison preserves the actual residue structure map. -/
@[reassoc] theorem zeroNodalProjectiveIso_structure :
    (e).hom ≫ pullback.fst _ _ = integralCurveStructure N := by
  apply (cancel_epi (yzPushoutIso N).hom).mp
  apply pushout.hom_ext
  · simp only [← Category.assoc, inl_yzPushoutIso]
    rw [Category.assoc, zeroNodalProjectiveIso_infinity_assoc, zeroNodalInfinityChart,
      Category.assoc, finiteInfinityTensorChart_structure, nodalResidueChartIso_structure,
      integralCurveChart_structure]
  · simp only [← Category.assoc, inr_yzPushoutIso]
    rw [Category.assoc, zeroNodalProjectiveIso_terminal_assoc,
      terminalZeroNodalChart_structure, integralCurveChart_structure]
    rfl

/-- The entire projective comparison is an isomorphism over the residue field. -/
def zeroNodalProjectiveOverIso : Over.mk (integralCurveStructure N) ≅
    Over.mk (pullback.fst q (finiteGlobalStructure hπ data j hj)) :=
  Over.isoMk e (zeroNodalProjectiveIso_structure hπ data D hdepth j hj hzero)

/-- Every original cubic function is retained by the entire projective comparison. -/
@[reassoc] theorem zeroNodalProjectiveIso_contraction :
    (e).hom ≫ pullback.snd q (finiteGlobalStructure hπ data j hj) ≫
      finiteGlobalContraction hπ data j hj = nodalResidueContraction D hdepth := by
  apply (cancel_epi (yzPushoutIso N).hom).mp
  apply pushout.hom_ext
  · simp only [← Category.assoc, inl_yzPushoutIso]
    simp only [Category.assoc]
    rw [zeroNodalProjectiveIso_infinity_assoc, zeroNodalInfinityChart, Category.assoc,
      finiteInfinityTensorChart_toCurve, integralCurveChart_nodalResidueContraction]
    change Spec.map _ ≫ Spec.map _ ≫ _ = Spec.map _ ≫ _
    rw [← Spec.map_comp_assoc]
    rfl
  · simp only [← Category.assoc, inr_yzPushoutIso]
    simp only [Category.assoc]
    rw [zeroNodalProjectiveIso_terminal_assoc, terminalZeroNodalChart_toCurve,
      integralCurveChart_nodalResidueContraction]
    change Spec.map _ ≫ _ = Spec.map _ ≫ _
    congr 2
    exact congrArg (fun f : WeierstrassIntegralChart.Coordinate W 2 →ₐ[R]
      WeierstrassIntegralChart.Coordinate N 2 => CommRingCat.ofHom f.toRingHom)
        (nodalResidueChartMap_coefficient D hdepth 2).symm

/-- The full Laurent normalization agrees with the nodal infinity chart on every function. -/
@[reassoc] theorem zeroNodalProjectiveIso_laurent :
    splitNodalTorusToCurve a ≫ (e).hom = infinityLaurentChart hπ data D hdepth j hj := by
  rw [splitNodalTorusToCurve, Category.assoc, zeroNodalProjectiveIso_infinity]
  change _ ≫ _ ≫ _ = _ ≫ _
  rw [← Category.assoc]
  congr 1
  change Spec.map _ ≫ Spec.map _ = Spec.map _
  rw [← Spec.map_comp]
  rfl

end FLT.Mazur.WeierstrassDividedDepth
