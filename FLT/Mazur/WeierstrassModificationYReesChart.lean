/-
Copyright (c) 2026 krandder. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: krandder
-/
module

public import FLT.Mazur.WeierstrassDilatationReesChart
public import FLT.Mazur.WeierstrassModificationYGenerators
public import FLT.Mazur.WeierstrassModificationYOriginalLocalization

/-!
# The y-direction chart is the original vertical Rees fraction chart

The center is the same ideal (s,x,y) in the original affine cubic used by
the other two charts. The comparison preserves the original contraction.
-/

@[expose] public noncomputable section

namespace FLT.Mazur.WeierstrassModificationY

set_option backward.isDefEq.respectTransparency false

universe u
variable {R : Type u} [CommRing R] (W : WeierstrassCurve R) (s b3 b4 b6 : R)
  (h3 : W.a₃ = s * b3) (h4 : W.a₄ = s * b4) (h6 : W.a₆ = s ^ 2 * b6)

/-- The vertical fraction algebra of the original center's Rees algebra. -/
def verticalReesChart : Subalgebra R (OriginalVerticalOpen W) :=
  (BlowupFractionChart.chart (WeierstrassDilatation.modificationCenter W s)
    (WeierstrassIntegralChart.coord W 2 1)).restrictScalars R

/-- The actual y-direction image equals the original vertical Rees fraction chart. -/
theorem toOriginalVerticalOpen_range :
    (toOriginalVerticalOpen W s b3 b4 b6 h3 h4 h6).range = verticalReesChart W s := by
  let f := toOriginalVerticalOpen W s b3 b4 b6 h3 h4 h6
  let A := WeierstrassIntegralChart.Coordinate W 2
  let d : OriginalVerticalOpen W :=
    IsLocalization.Away.invSelf (WeierstrassIntegralChart.coord W 2 1)
  have hr (a : A) (ha : a ∈ ({algebraMap R A s,
      WeierstrassIntegralChart.coord W 2 0, WeierstrassIntegralChart.coord W 2 1} : Set A)) :
      algebraMap A (OriginalVerticalOpen W) a * d ∈ verticalReesChart W s := by
    change _ ∈ BlowupFractionChart.chart (WeierstrassDilatation.modificationCenter W s)
      (WeierstrassIntegralChart.coord W 2 1)
    rw [WeierstrassDilatation.modificationCenter, BlowupFractionChart.chart_span]
    exact Algebra.subset_adjoin ⟨a, ha, rfl⟩
  apply le_antisymm
  · apply range_le_of_coordinates
    intro i
    fin_cases i
    · change f (coord W s b3 b4 b6 0) ∈ _
      dsimp only [f]
      rw [toOriginalVerticalOpen, fractionMap_coord]
      change d * algebraMap R (OriginalVerticalOpen W) s ∈ _
      rw [IsScalarTower.algebraMap_apply R A (OriginalVerticalOpen W), mul_comm]
      exact hr _ (Set.mem_insert _ _)
    · change f (coord W s b3 b4 b6 1) ∈ _
      dsimp only [f]
      rw [toOriginalVerticalOpen, fractionMap_coord]
      change d * algebraMap A (OriginalVerticalOpen W)
        (WeierstrassIntegralChart.coord W 2 0) ∈ _
      rw [mul_comm]
      exact hr _ (by simp)
    · change f (coord W s b3 b4 b6 2) ∈ _
      dsimp only [f]
      rw [toOriginalVerticalOpen, fractionMap_coord]
      change algebraMap A (OriginalVerticalOpen W)
        (WeierstrassIntegralChart.coord W 2 1) ∈
          BlowupFractionChart.chart (WeierstrassDilatation.modificationCenter W s)
            (WeierstrassIntegralChart.coord W 2 1)
      exact (BlowupFractionChart.chart (WeierstrassDilatation.modificationCenter W s)
        (WeierstrassIntegralChart.coord W 2 1)).algebraMap_mem _
  · intro z hz
    change z ∈ BlowupFractionChart.chart (WeierstrassDilatation.modificationCenter W s)
      (WeierstrassIntegralChart.coord W 2 1) at hz
    rw [WeierstrassDilatation.modificationCenter, BlowupFractionChart.chart_span] at hz
    induction hz using Algebra.adjoin_induction with
    | mem z hz =>
      rcases hz with ⟨a, ha, rfl⟩
      rcases Set.mem_insert_iff.mp ha with rfl | ha
      · refine ⟨coord W s b3 b4 b6 0, ?_⟩
        change f (coord W s b3 b4 b6 0) = _
        dsimp only [f]
        rw [toOriginalVerticalOpen, fractionMap_coord]
        change d * algebraMap R (OriginalVerticalOpen W) s = _
        rw [IsScalarTower.algebraMap_apply R A (OriginalVerticalOpen W)]
        exact mul_comm _ _
      · rcases Set.mem_insert_iff.mp ha with rfl | ha
        · refine ⟨coord W s b3 b4 b6 1, ?_⟩
          change f (coord W s b3 b4 b6 1) = _
          dsimp only [f]
          rw [toOriginalVerticalOpen, fractionMap_coord]
          exact mul_comm _ _
        · have ha' := Set.mem_singleton_iff.mp ha
          subst a
          change algebraMap A (OriginalVerticalOpen W)
            (WeierstrassIntegralChart.coord W 2 1) * d ∈ f.range
          have he : algebraMap A (OriginalVerticalOpen W)
              (WeierstrassIntegralChart.coord W 2 1) * d = 1 :=
            IsLocalization.Away.mul_invSelf _
          rw [he]
          exact f.range.one_mem
    | algebraMap a =>
      refine ⟨fromOriginal W s b3 b4 b6 h3 h4 h6 a, ?_⟩
      exact congrArg (fun k : A →ₐ[R] OriginalVerticalOpen W => k a)
        (toOriginalVerticalOpen_fromOriginal W s b3 b4 b6 h3 h4 h6)
    | add a b ha hb ih ih' => exact f.range.add_mem ih ih'
    | mul a b ha hb ih ih' => exact f.range.mul_mem ih ih'

/-- The actual y-direction algebra is the original vertical Rees fraction algebra. -/
def verticalReesChartEquiv [IsDomain R] [IsBezout R] (hs : s ≠ 0) :
    Coordinate W s b3 b4 b6 ≃ₐ[R] verticalReesChart W s :=
  (AlgEquiv.ofInjective (toOriginalVerticalOpen W s b3 b4 b6 h3 h4 h6)
    (toOriginalVerticalOpen_injective W s b3 b4 b6 h3 h4 h6 hs)).trans
      (Subalgebra.equivOfEq _ _ (toOriginalVerticalOpen_range W s b3 b4 b6 h3 h4 h6))

/-- The Rees comparison retains the contraction on every original function. -/
theorem verticalReesChartEquiv_fromOriginal [IsDomain R] [IsBezout R] (hs : s ≠ 0)
    (a : WeierstrassIntegralChart.Coordinate W 2) :
    (verticalReesChartEquiv W s b3 b4 b6 h3 h4 h6 hs
      (fromOriginal W s b3 b4 b6 h3 h4 h6 a) : OriginalVerticalOpen W) =
        algebraMap (WeierstrassIntegralChart.Coordinate W 2) (OriginalVerticalOpen W) a :=
  congrArg (fun k : WeierstrassIntegralChart.Coordinate W 2 →ₐ[R] OriginalVerticalOpen W => k a)
    (toOriginalVerticalOpen_fromOriginal W s b3 b4 b6 h3 h4 h6)

end FLT.Mazur.WeierstrassModificationY
