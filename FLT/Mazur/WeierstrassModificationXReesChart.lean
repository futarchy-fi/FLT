/-
Copyright (c) 2026 krandder. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: krandder
-/
module

public import FLT.Mazur.BlowupFractionChart
public import FLT.Mazur.WeierstrassDilatationReesChart
public import FLT.Mazur.WeierstrassModificationXGenerators
public import FLT.Mazur.WeierstrassModificationXOriginalLocalization

/-!
# The x-direction chart is the original horizontal Rees fraction chart

The center remains the ideal (s,x,y) in the original affine cubic. Its
horizontal fraction chart is explicitly isomorphic to the actual x-direction
equation algebra, retaining contraction and both original ratios.
-/

@[expose] public noncomputable section

namespace FLT.Mazur.WeierstrassModificationX

set_option backward.isDefEq.respectTransparency false

universe u
variable {R : Type u} [CommRing R] (W : WeierstrassCurve R) (s b3 b4 b6 : R)
  (h3 : W.a₃ = s * b3) (h4 : W.a₄ = s * b4) (h6 : W.a₆ = s ^ 2 * b6)

/-- The horizontal fraction algebra of the original center's Rees algebra. -/
def horizontalReesChart : Subalgebra R (OriginalHorizontalOpen W) :=
  (BlowupFractionChart.chart (WeierstrassDilatation.modificationCenter W s)
    (WeierstrassIntegralChart.coord W 2 0)).restrictScalars R

/-- The image of the actual x-direction chart equals the horizontal fraction Rees chart. -/
theorem toOriginalHorizontalOpen_range :
    (toOriginalHorizontalOpen W s b3 b4 b6 h3 h4 h6).range = horizontalReesChart W s := by
  let f := toOriginalHorizontalOpen W s b3 b4 b6 h3 h4 h6
  let A := WeierstrassIntegralChart.Coordinate W 2
  let d : OriginalHorizontalOpen W :=
    IsLocalization.Away.invSelf (WeierstrassIntegralChart.coord W 2 0)
  have hr (a : A) (ha : a ∈ ({algebraMap R A s,
      WeierstrassIntegralChart.coord W 2 0, WeierstrassIntegralChart.coord W 2 1} : Set A)) :
      algebraMap A (OriginalHorizontalOpen W) a * d ∈ horizontalReesChart W s := by
    change _ ∈ BlowupFractionChart.chart (WeierstrassDilatation.modificationCenter W s)
      (WeierstrassIntegralChart.coord W 2 0)
    rw [WeierstrassDilatation.modificationCenter, BlowupFractionChart.chart_span]
    exact Algebra.subset_adjoin ⟨a, ha, rfl⟩
  apply le_antisymm
  · apply range_le_of_coordinates
    · rw [toOriginalHorizontalOpen, fractionMap_t]
      rw [IsScalarTower.algebraMap_apply R A (OriginalHorizontalOpen W)]
      change d * algebraMap A (OriginalHorizontalOpen W) (algebraMap R A s) ∈ _
      rw [mul_comm]
      exact hr _ (Set.mem_insert _ _)
    · rw [toOriginalHorizontalOpen, fractionMap_v]
      change d * algebraMap A (OriginalHorizontalOpen W)
        (WeierstrassIntegralChart.coord W 2 1) ∈ horizontalReesChart W s
      rw [mul_comm]
      exact hr _ (by simp)
  · intro z hz
    change z ∈ BlowupFractionChart.chart (WeierstrassDilatation.modificationCenter W s)
      (WeierstrassIntegralChart.coord W 2 0) at hz
    rw [WeierstrassDilatation.modificationCenter, BlowupFractionChart.chart_span] at hz
    induction hz using Algebra.adjoin_induction with
    | mem z hz =>
      rcases hz with ⟨a, ha, rfl⟩
      rcases Set.mem_insert_iff.mp ha with rfl | ha
      · refine ⟨t W s b3 b4 b6, ?_⟩
        change f (t W s b3 b4 b6) = _
        dsimp only [f]
        rw [toOriginalHorizontalOpen, fractionMap_t]
        rw [IsScalarTower.algebraMap_apply R A (OriginalHorizontalOpen W)]
        exact mul_comm _ _
      · rcases Set.mem_insert_iff.mp ha with rfl | ha
        · change algebraMap A (OriginalHorizontalOpen W)
            (WeierstrassIntegralChart.coord W 2 0) * d ∈ f.range
          have he : algebraMap A (OriginalHorizontalOpen W)
              (WeierstrassIntegralChart.coord W 2 0) * d = 1 :=
            IsLocalization.Away.mul_invSelf _
          rw [he]
          exact f.range.one_mem
        · have ha' := Set.mem_singleton_iff.mp ha
          subst a
          refine ⟨v W s b3 b4 b6, ?_⟩
          change f (v W s b3 b4 b6) = _
          dsimp only [f]
          rw [toOriginalHorizontalOpen, fractionMap_v]
          exact mul_comm _ _
    | algebraMap a =>
      refine ⟨fromOriginal W s b3 b4 b6 h3 h4 h6 a, ?_⟩
      exact congrArg (fun k : A →ₐ[R] OriginalHorizontalOpen W => k a)
        (toOriginalHorizontalOpen_fromOriginal W s b3 b4 b6 h3 h4 h6)
    | add a b ha hb ih ih' => exact f.range.add_mem ih ih'
    | mul a b ha hb ih ih' => exact f.range.mul_mem ih ih'

/-- The actual x-direction algebra is isomorphic to the original Rees fraction algebra. -/
def horizontalReesChartEquiv [IsDomain R] (hs : s ≠ 0) :
    Coordinate W s b3 b4 b6 ≃ₐ[R] horizontalReesChart W s :=
  (AlgEquiv.ofInjective (toOriginalHorizontalOpen W s b3 b4 b6 h3 h4 h6)
    (toOriginalHorizontalOpen_injective W s b3 b4 b6 h3 h4 h6 hs)).trans
      (Subalgebra.equivOfEq _ _ (toOriginalHorizontalOpen_range W s b3 b4 b6 h3 h4 h6))

/-- The Rees comparison preserves the original contraction on every original function. -/
theorem horizontalReesChartEquiv_fromOriginal [IsDomain R] (hs : s ≠ 0)
    (a : WeierstrassIntegralChart.Coordinate W 2) :
    (horizontalReesChartEquiv W s b3 b4 b6 h3 h4 h6 hs
      (fromOriginal W s b3 b4 b6 h3 h4 h6 a) : OriginalHorizontalOpen W) =
        algebraMap (WeierstrassIntegralChart.Coordinate W 2) (OriginalHorizontalOpen W) a :=
  congrArg (fun k : WeierstrassIntegralChart.Coordinate W 2 →ₐ[R] OriginalHorizontalOpen W => k a)
    (toOriginalHorizontalOpen_fromOriginal W s b3 b4 b6 h3 h4 h6)

end FLT.Mazur.WeierstrassModificationX
