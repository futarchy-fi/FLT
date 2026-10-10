/-
Copyright (c) 2026 krandder. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: krandder
-/
module

public import FLT.Mazur.BlowupFractionChart
public import FLT.Mazur.WeierstrassDilatationGenerators
public import FLT.Mazur.WeierstrassSuccessiveScaleEmbedding
public import FLT.Mazur.WeierstrassSuccessiveXReesChart

/-!
# The deeper divided algebra is the successive scale Rees chart

The comparison uses the same center (π,x,y) as the successive horizontal
chart. It retains refinement to the preceding divided equation algebra.
-/

@[expose] public noncomputable section

namespace FLT.Mazur.WeierstrassSuccessiveScale

set_option backward.isDefEq.respectTransparency false

universe u
variable {R : Type u} [CommRing R] (W : WeierstrassCurve R) (s π b3 b4 b6 : R)
local notation "B" =>
  WeierstrassDilatation.Coordinate W s (π * b3) (π * b4) (π ^ 2 * b6)
local notation "BX" => WeierstrassDilatation.x W s (π * b3) (π * b4) (π ^ 2 * b6)
local notation "BY" => WeierstrassDilatation.y W s (π * b3) (π * b4) (π ^ 2 * b6)
local notation "D" => WeierstrassDilatation.Coordinate W (s * π) b3 b4 b6
local notation "DX" => WeierstrassDilatation.x W (s * π) b3 b4 b6
local notation "DY" => WeierstrassDilatation.y W (s * π) b3 b4 b6
local notation "I" => WeierstrassSuccessiveX.modificationCenter W s π b3 b4 b6
local notation "ref" => WeierstrassDilatation.refinement W s π
  (π * b3) (π * b4) (π ^ 2 * b6) b3 b4 b6 rfl rfl rfl

/-- The scale fraction algebra of the original center's Rees algebra. -/
def scaleReesChart : Subalgebra R (PreviousScaleOpen W s π b3 b4 b6) :=
  (BlowupFractionChart.chart I
    (algebraMap R B π)).restrictScalars R

/-- The image of the actual divided chart equals the scale fraction Rees chart. -/
theorem toPreviousScaleOpen_range :
    (toPreviousScaleOpen W s π b3 b4 b6).range = scaleReesChart W s π b3 b4 b6 := by
  let f := toPreviousScaleOpen W s π b3 b4 b6
  let A := B
  let d : PreviousScaleOpen W s π b3 b4 b6 := IsLocalization.Away.invSelf (algebraMap R A π)
  have hr (a : B) (ha : a ∈ ({algebraMap R B π, BX, BY} : Set B)) :
      algebraMap B (PreviousScaleOpen W s π b3 b4 b6) a * d ∈
        scaleReesChart W s π b3 b4 b6 := by
    change _ ∈ BlowupFractionChart.chart I (algebraMap R B π)
    rw [WeierstrassSuccessiveX.modificationCenter, BlowupFractionChart.chart_span]
    exact Algebra.subset_adjoin ⟨a, ha, rfl⟩
  apply le_antisymm
  · apply WeierstrassDilatation.range_le_of_coordinates
    · rw [toPreviousScaleOpen, fractionMap_x]
      change d * algebraMap A (PreviousScaleOpen W s π b3 b4 b6)
        BX ∈ scaleReesChart W s π b3 b4 b6
      rw [mul_comm d]
      exact hr BX (by simp)
    · rw [toPreviousScaleOpen, fractionMap_y]
      change d * algebraMap A (PreviousScaleOpen W s π b3 b4 b6)
        BY ∈ scaleReesChart W s π b3 b4 b6
      rw [mul_comm d]
      exact hr BY (by simp)
  · intro z hz
    change z ∈ BlowupFractionChart.chart I (algebraMap R A π) at hz
    rw [WeierstrassSuccessiveX.modificationCenter, BlowupFractionChart.chart_span] at hz
    induction hz using Algebra.adjoin_induction with
    | mem z hz =>
      rcases hz with ⟨a, ha, rfl⟩
      rcases Set.mem_insert_iff.mp ha with rfl | ha
      · change algebraMap A (PreviousScaleOpen W s π b3 b4 b6) (algebraMap R A π) * d ∈ f.range
        have he : algebraMap A (PreviousScaleOpen W s π b3 b4 b6) (algebraMap R A π) * d = 1 :=
          IsLocalization.Away.mul_invSelf _
        rw [he]
        exact f.range.one_mem
      · rcases Set.mem_insert_iff.mp ha with rfl | ha
        · refine ⟨DX, ?_⟩
          change f DX = _
          dsimp only [f]
          rw [toPreviousScaleOpen, fractionMap_x]
          exact mul_comm _ _
        · have ha' := Set.mem_singleton_iff.mp ha
          subst a
          refine ⟨DY, ?_⟩
          change f DY = _
          dsimp only [f]
          rw [toPreviousScaleOpen, fractionMap_y]
          exact mul_comm _ _
    | algebraMap a =>
      refine ⟨ref a, ?_⟩
      exact congrArg (fun k : A →ₐ[R] PreviousScaleOpen W s π b3 b4 b6 => k a)
        (toPreviousScaleOpen_refinement W s π b3 b4 b6)
    | add a b ha hb ih ih' => exact f.range.add_mem ih ih'
    | mul a b ha hb ih ih' => exact f.range.mul_mem ih ih'

/-- The actual divided algebra is isomorphic to the original Rees fraction algebra. -/
def scaleReesChartEquiv (hπ : IsRegular π) :
    D ≃ₐ[R] scaleReesChart W s π b3 b4 b6 :=
  (AlgEquiv.ofInjective (toPreviousScaleOpen W s π b3 b4 b6)
    (toPreviousScaleOpen_injective W s π b3 b4 b6 hπ)).trans
      (Subalgebra.equivOfEq _ _ (toPreviousScaleOpen_range W s π b3 b4 b6))

/-- The Rees comparison preserves the original contraction on every original function. -/
theorem scaleReesChartEquiv_refinement (hπ : IsRegular π)
    (a : B) :
    (scaleReesChartEquiv W s π b3 b4 b6 hπ
      (ref a) : PreviousScaleOpen W s π b3 b4 b6) =
        algebraMap B (PreviousScaleOpen W s π b3 b4 b6) a :=
  congrArg (fun k : B →ₐ[R] PreviousScaleOpen W s π b3 b4 b6 => k a)
    (toPreviousScaleOpen_refinement W s π b3 b4 b6)

end FLT.Mazur.WeierstrassSuccessiveScale
