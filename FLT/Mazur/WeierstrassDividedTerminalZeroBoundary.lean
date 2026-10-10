/-
Copyright (c) 2026 krandder. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: krandder
-/
module

public import FLT.Mazur.WeierstrassDilatationZeroResidueBoundary
public import FLT.Mazur.WeierstrassDividedTerminalZeroNodalChart
public import FLT.Mazur.WeierstrassDividedTensorYBoundary

/-!
# The full zero-depth terminal boundary inside the global residue model

The complete nodal Y-boundary agrees with the actual original tensor Y/Z
transition at infinity. Equality holds as scheme morphisms on every function.
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
local notation "N" => splitNodalEquation (residueTangentUnit D)
local notation "b" => nodalResidueBoundaryIso D hdepth 2 1
local notation "q" => Spec.map (CommRingCat.ofHom (algebraMap R K))
local notation "d" => data (Fin.mk j (Nat.lt_succ_of_le hj))
local notation "z" => terminalZeroNodalChart hπ data D hdepth j hj hzero

/-- The whole nodal Y-boundary maps to the retained infinity tensor algebra. -/
def terminalZeroBoundaryToInfinity := (b).hom ≫ tensorBoundaryToInfinity (W := W) K

instance terminalZeroBoundaryToInfinity_isOpenImmersion :
    IsOpenImmersion (terminalZeroBoundaryToInfinity D hdepth) :=
  inferInstanceAs (IsOpenImmersion (_ ≫ _))

/-- The entire boundary lifts through the unchanged original chart at infinity. -/
theorem terminalZeroBoundary_integral_square :
    (b).hom ≫ TensorOpenChart.projection ≫ affineBoundaryToY W ≫
        finiteInfinityChart hπ data j hj =
      overlapInclusion N 2 1 ≫ z ≫ pullback.snd q (finiteGlobalStructure hπ data j hj) := by
  let u := (b).hom ≫ TensorOpenChart.projection ≫ affineBoundaryToY W
  let v := overlapInclusion N 2 1 ≫ z ≫
    pullback.snd q (finiteGlobalStructure hπ data j hj)
  have hc : u ≫ integralCurveChart W 1 = v ≫ finiteGlobalContraction hπ data j hj := by
    dsimp only [u, v]
    simp only [Category.assoc]
    rw [terminalZeroNodalChart_toCurve]
    change _ = overlapInclusion N 2 1 ≫
      Spec.map (CommRingCat.ofHom (zeroResidueOriginalMap D hdepth).toRingHom) ≫
        integralCurveChart W 2
    rw [← zeroResidueBoundary_original_assoc]
    exact congrArg (fun f => (b).hom ≫ TensorOpenChart.projection ≫ f) (yz_isPullback W).w
  let pb := finiteInfinity_isPullback hπ data j hj
  have hf := pb.lift_fst u v hc
  have hg := pb.lift_snd u v hc
  simp only [Category.comp_id] at hf
  rw [hf] at hg
  simpa only [u, v, Category.assoc] using hg

/-- Both inclusions are the same on the whole original nodal boundary. -/
@[reassoc] theorem terminalZeroBoundary_overlap :
    terminalZeroBoundaryToInfinity D hdepth ≫ finiteInfinityTensorChart hπ data K j hj =
      overlapInclusion N 2 1 ≫ z := by
  apply pullback.hom_ext
  · simp only [Category.assoc]
    rw [finiteInfinityTensorChart_structure, terminalZeroNodalChart_structure]
    rw [terminalZeroBoundaryToInfinity, Category.assoc, tensorBoundaryToInfinity_structure,
      nodalResidueBoundaryIso_structure]
    change Spec.map _ = Spec.map _ ≫ Spec.map _
    rw [← Spec.map_comp]
    congr 1
  · simp only [Category.assoc]
    change terminalZeroBoundaryToInfinity D hdepth ≫
      (TensorOpenChart.chart _ _ _ ≫ pullback.snd _ _) = _
    rw [TensorOpenChart.chart_snd, terminalZeroBoundaryToInfinity, Category.assoc,
      tensorBoundaryToInfinity_projection_assoc]
    exact terminalZeroBoundary_integral_square hπ data D hdepth j hj hzero

end FLT.Mazur.WeierstrassDividedDepth
