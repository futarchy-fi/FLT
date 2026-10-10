/-
Copyright (c) 2026 krandder. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: krandder
-/
module

public import FLT.Mazur.WeierstrassDividedInitialZeroSlopeChart
public import FLT.Mazur.WeierstrassModificationXZeroResidueInfinity

/-!
# The whole start-zero slope chart in the retained global infinity chart

The original infinity transition lifts through the proved cartesian squares
of the projective modification and its tensor chart. Thus the entire initial
slope chart lies in the retained infinity open with its actual inclusion.
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
  (D : SplitNodeDepth W π depth) (hdepth : 0 < depth) (hstart : start = 0)
  (j : ℕ) (hj : j ≤ n)
open WeierstrassModificationX
open scoped TensorProduct
local notation "K" => ResidueField R
local notation "d₀" => data (Fin.mk 0 (Nat.zero_lt_succ n))
local notation "P" => SlopeOpen (residue R W.a₁)
local notation "infinity" => zeroResidueToInfinity D hdepth start hstart
  (Data.b3 d₀) (Data.b4 d₀) (Data.b6 d₀)
  (Data.factor3 d₀) (Data.factor4 d₀) (Data.factor6 d₀)
local notation "slopeChart" => initialZeroSlopeChart hπ data D hdepth hstart j hj
local notation "q" => Spec.map (CommRingCat.ofHom (algebraMap R K))

/-- The whole original slope transition lands in the unchanged integral infinity chart. -/
theorem initialZeroInfinity_square :
    infinity ≫ finiteInfinityChart hπ data j hj =
      slopeChart ≫ pullback.snd q (finiteGlobalStructure hπ data j hj) := by
  have hc : infinity ≫ WeierstrassIntegralChart.integralCurveChart W 1 =
      (slopeChart ≫ pullback.snd q (finiteGlobalStructure hπ data j hj)) ≫
        finiteGlobalContraction hπ data j hj := by
    rw [Category.assoc, initialZeroSlopeChart_toCurve]
    exact zeroResidueToInfinity_contraction D hdepth start hstart
      (Data.b3 d₀) (Data.b4 d₀) (Data.b6 d₀)
      (Data.factor3 d₀) (Data.factor4 d₀) (Data.factor6 d₀)
  let pb := finiteInfinity_isPullback hπ data j hj
  have hf := pb.lift_fst infinity
    (slopeChart ≫ pullback.snd q (finiteGlobalStructure hπ data j hj)) hc
  have hg := pb.lift_snd infinity
    (slopeChart ≫ pullback.snd q (finiteGlobalStructure hπ data j hj)) hc
  simp only [Category.comp_id] at hf
  rw [hf] at hg
  exact hg

/-- The entire initial slope chart maps to the actual retained tensor infinity algebra. -/
def initialZeroToTensorInfinity : Spec (.of P) ⟶
    Spec (.of (K ⊗[R] WeierstrassIntegralChart.Coordinate W 1)) :=
  (finiteInfinityTensorChart_isPullback hπ data K j hj).lift slopeChart infinity
    (initialZeroInfinity_square hπ data D hdepth hstart j hj).symm

/-- The lifted transition is exactly the original global slope inclusion. -/
@[reassoc] theorem initialZeroToTensorInfinity_chart :
    initialZeroToTensorInfinity hπ data D hdepth hstart j hj ≫
      finiteInfinityTensorChart hπ data K j hj = slopeChart :=
  (finiteInfinityTensorChart_isPullback hπ data K j hj).lift_fst _ _ _

/-- The lifted transition still projects to the original Y/Z coordinate transition. -/
@[reassoc] theorem initialZeroToTensorInfinity_projection :
    initialZeroToTensorInfinity hπ data D hdepth hstart j hj ≫
      TensorOpenChart.projection = infinity :=
  (finiteInfinityTensorChart_isPullback hπ data K j hj).lift_snd _ _ _

/-- No point of the original initial chart lies outside the retained infinity chart. -/
theorem initialZeroSlopeChart_range_subset_infinity :
    Set.range slopeChart ⊆ Set.range (finiteInfinityTensorChart hπ data K j hj) := by
  rintro z ⟨x, rfl⟩
  refine ⟨initialZeroToTensorInfinity hπ data D hdepth hstart j hj x, ?_⟩
  exact congrArg (fun f => f x)
    (initialZeroToTensorInfinity_chart hπ data D hdepth hstart j hj)

include D hdepth hstart in
/-- At start zero the complete atlas covers without its redundant last initial chart. -/
theorem zeroStartAtlas_cover_without_initial (z : finiteGlobalTensorModel hπ data K j hj) :
    ∃ i : Fin (j + 3), ∃ x, i.val < j + 2 ∧ globalTensorAtlasMap hπ data K j hj i x = z := by
  obtain ⟨i, x, rfl⟩ := globalTensorAtlas_cover hπ data K j hj z
  by_cases hi : i.val = j + 2
  · have hi' : i = Fin.succ ⟨j + 1, Nat.lt_succ_self (j + 1)⟩ := Fin.ext hi
    subst i
    obtain ⟨y, hy⟩ :=
      (initialZeroSlopeAtlasIso hπ data D hdepth hstart j hj).hom.homeomorph.surjective x
    change (initialZeroSlopeAtlasIso hπ data D hdepth hstart j hj).hom y = x at hy
    have hy' : slopeChart y =
        globalTensorAtlasMap hπ data K j hj (Fin.succ ⟨j + 1, by omega⟩) x := by
      rw [← initialZeroSlopeAtlasIso_map hπ data D hdepth hstart j hj]
      change globalTensorAtlasMap hπ data K j hj _
        ((initialZeroSlopeAtlasIso hπ data D hdepth hstart j hj).hom y) = _
      rw [hy]
    obtain ⟨w, hw⟩ := initialZeroSlopeChart_range_subset_infinity
      hπ data D hdepth hstart j hj ⟨y, hy'⟩
    exact ⟨0, w, by change 0 < j + 2; omega, hw⟩
  · exact ⟨i, x, by omega, rfl⟩

/-- The retained infinity chart and all noninitial charts give a smaller finite open cover. -/
def zeroStartReducedOpenCover : (finiteGlobalTensorModel hπ data K j hj).OpenCover where
  I₀ := {i : Fin (j + 3) // i.val < j + 2}
  X i := globalTensorAtlasObject hπ data K j hj i.val
  f i := globalTensorAtlasMap hπ data K j hj i.val
  mem₀ := by
    rw [Scheme.presieve₀_mem_precoverage_iff]
    refine ⟨?_, fun i => globalTensorAtlasMap_isOpenImmersion hπ data K j hj i.val⟩
    intro z
    obtain ⟨i, x, hi, hx⟩ := zeroStartAtlas_cover_without_initial hπ data D hdepth hstart j hj z
    exact ⟨⟨i, hi⟩, x, hx⟩

instance zeroStartReducedOpenCover_finite :
    Finite (zeroStartReducedOpenCover hπ data D hdepth hstart j hj).I₀ := by
  change Finite {i : Fin (j + 3) // i.val < j + 2}
  infer_instance

/-- Every surviving chart retains its original global inclusion. -/
theorem zeroStartReducedOpenCover_map (i : {i : Fin (j + 3) // i.val < j + 2}) :
    (zeroStartReducedOpenCover hπ data D hdepth hstart j hj).f i =
      globalTensorAtlasMap hπ data K j hj i.val := rfl

end FLT.Mazur.WeierstrassDividedDepth
