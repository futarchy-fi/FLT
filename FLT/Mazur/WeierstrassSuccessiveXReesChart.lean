/-
Copyright (c) 2026 krandder. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: krandder
-/
module

public import FLT.Mazur.BlowupFractionChart
public import FLT.Mazur.WeierstrassSuccessiveXGenerators
public import FLT.Mazur.WeierstrassSuccessiveXFractionEmbedding

/-!
# The successive x-chart is the preceding horizontal Rees fraction chart

The center is the ideal (π,x,y) in the preceding divided cubic. Its
horizontal fraction chart is explicitly isomorphic to the actual x-direction
equation algebra, retaining contraction and both original ratios.
-/

@[expose] public noncomputable section

namespace FLT.Mazur.WeierstrassSuccessiveX

set_option backward.isDefEq.respectTransparency false

universe u
variable {R : Type u} [CommRing R] (W : WeierstrassCurve R) (s π b3 b4 b6 : R)

local notation "B" =>
  WeierstrassDilatation.Coordinate W s (π * b3) (π * b4) (π ^ 2 * b6)
local notation "BX" => WeierstrassDilatation.x W s (π * b3) (π * b4) (π ^ 2 * b6)
local notation "BY" => WeierstrassDilatation.y W s (π * b3) (π * b4) (π ^ 2 * b6)
local notation "L" => PreviousHorizontalOpen W s π b3 b4 b6

/-- The center of this step lies in the preceding actual divided cubic. -/
def modificationCenter : Ideal B :=
  Ideal.span {algebraMap R _ π, BX, BY}

/-- The horizontal fraction algebra of the original center's Rees algebra. -/
def horizontalReesChart : Subalgebra R L :=
  (BlowupFractionChart.chart (modificationCenter W s π b3 b4 b6)
    BX).restrictScalars R

/-- The image of the actual x-direction chart equals the horizontal fraction Rees chart. -/
theorem toPreviousHorizontalOpen_range :
    (toPreviousHorizontalOpen W s π b3 b4 b6).range = horizontalReesChart W s π b3 b4 b6 := by
  let f := toPreviousHorizontalOpen W s π b3 b4 b6
  let A := B
  let d : L := IsLocalization.Away.invSelf BX
  have hr (a : A) (ha : a ∈ ({algebraMap R A π,
      BX, BY} : Set A)) :
      algebraMap A L a * d ∈ horizontalReesChart W s π b3 b4 b6 := by
    change _ ∈ BlowupFractionChart.chart (modificationCenter W s π b3 b4 b6)
      BX
    rw [modificationCenter, BlowupFractionChart.chart_span]
    exact Algebra.subset_adjoin ⟨a, ha, rfl⟩
  apply le_antisymm
  · apply range_le_of_coordinates
    intro i
    fin_cases i
    · change toPreviousHorizontalOpen W s π b3 b4 b6
        (coord W s π b3 b4 b6 0) ∈ _
      rw [toPreviousHorizontalOpen_t]
      rw [IsScalarTower.algebraMap_apply R A L]
      change algebraMap A L
        (algebraMap R A π) * d ∈ _
      exact hr _ (Set.mem_insert _ _)
    · change toPreviousHorizontalOpen W s π b3 b4 b6
        (coord W s π b3 b4 b6 1) ∈ _
      rw [toPreviousHorizontalOpen_v]
      change d * algebraMap A L
        BY ∈ horizontalReesChart W s π b3 b4 b6
      rw [mul_comm d]
      exact hr _ (by simp)
    · change toPreviousHorizontalOpen W s π b3 b4 b6
        (coord W s π b3 b4 b6 2) ∈ _
      rw [toPreviousHorizontalOpen_u]
      exact (BlowupFractionChart.chart (modificationCenter W s π b3 b4 b6)
        BX).algebraMap_mem _
  · intro z hz
    change z ∈ BlowupFractionChart.chart (modificationCenter W s π b3 b4 b6)
      BX at hz
    rw [modificationCenter, BlowupFractionChart.chart_span] at hz
    induction hz using Algebra.adjoin_induction with
    | mem z hz =>
      rcases hz with ⟨a, ha, rfl⟩
      rcases Set.mem_insert_iff.mp ha with rfl | ha
      · refine ⟨coord W s π b3 b4 b6 0, ?_⟩
        change f (coord W s π b3 b4 b6 0) = _
        dsimp only [f]
        rw [toPreviousHorizontalOpen_t]
        rw [IsScalarTower.algebraMap_apply R A L]
      · rcases Set.mem_insert_iff.mp ha with rfl | ha
        · change algebraMap A L
            BX * d ∈ f.range
          have he : algebraMap A L
              BX * d = 1 :=
            IsLocalization.Away.mul_invSelf _
          rw [he]
          exact f.range.one_mem
        · have ha' := Set.mem_singleton_iff.mp ha
          subst a
          refine ⟨coord W s π b3 b4 b6 1, ?_⟩
          change f (coord W s π b3 b4 b6 1) = _
          dsimp only [f]
          rw [toPreviousHorizontalOpen_v]
          exact mul_comm _ _
    | algebraMap a =>
      refine ⟨fromDivided W s π b3 b4 b6 a, ?_⟩
      exact congrArg (fun k : A →ₐ[R] L => k a)
        (toPreviousHorizontalOpen_fromDivided W s π b3 b4 b6)
    | add a b ha hb ih ih' => exact f.range.add_mem ih ih'
    | mul a b ha hb ih ih' => exact f.range.mul_mem ih ih'

/-- The actual x-direction algebra is isomorphic to the original Rees fraction algebra. -/
def horizontalReesChartEquiv [IsDomain R] (hπ : π ≠ 0) :
    Coordinate W s π b3 b4 b6 ≃ₐ[R] horizontalReesChart W s π b3 b4 b6 :=
  (AlgEquiv.ofInjective (toPreviousHorizontalOpen W s π b3 b4 b6)
    (toPreviousHorizontalOpen_injective W s π b3 b4 b6 hπ)).trans
      (Subalgebra.equivOfEq _ _ (toPreviousHorizontalOpen_range W s π b3 b4 b6))

/-- The Rees comparison preserves the original contraction on every original function. -/
theorem horizontalReesChartEquiv_fromDivided [IsDomain R] (hπ : π ≠ 0)
    (a : B) :
    (horizontalReesChartEquiv W s π b3 b4 b6 hπ
      (fromDivided W s π b3 b4 b6 a) : L) =
        algebraMap B L a :=
  congrArg (fun k : B →ₐ[R] L => k a)
    (toPreviousHorizontalOpen_fromDivided W s π b3 b4 b6)

end FLT.Mazur.WeierstrassSuccessiveX
