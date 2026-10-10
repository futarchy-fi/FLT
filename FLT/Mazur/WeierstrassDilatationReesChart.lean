/-
Copyright (c) 2026 krandder. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: krandder
-/
module

public import FLT.Mazur.BlowupFractionChart
public import FLT.Mazur.WeierstrassDilatationGenerators
public import FLT.Mazur.WeierstrassDilatationLocalization

/-!
# The divided chart is the actual scale fraction chart of the Rees algebra

The center in the original affine cubic is (s,x,y). Its scale fraction algebra
is compared with the actual divided equation algebra by the original x/s and
y/s substitution. The comparison preserves contraction and requires only a
regular scale; it does not assert a global projective blowup identification.
-/

@[expose] public noncomputable section

namespace FLT.Mazur.WeierstrassDilatation

set_option backward.isDefEq.respectTransparency false

universe u
variable {R : Type u} [CommRing R] (W : WeierstrassCurve R) (s b3 b4 b6 : R)
  (h3 : W.a₃ = s * b3) (h4 : W.a₄ = s * b4) (h6 : W.a₆ = s ^ 2 * b6)

/-- The actual center ideal in the original affine cubic. -/
def modificationCenter : Ideal (WeierstrassIntegralChart.Coordinate W 2) :=
  Ideal.span {algebraMap R _ s, WeierstrassIntegralChart.coord W 2 0,
    WeierstrassIntegralChart.coord W 2 1}

/-- The scale fraction algebra of the original center's Rees algebra. -/
def scaleReesChart : Subalgebra R (OriginalScaleOpen W s) :=
  (BlowupFractionChart.chart (modificationCenter W s)
    (algebraMap R (WeierstrassIntegralChart.Coordinate W 2) s)).restrictScalars R

/-- The image of the actual divided chart equals the scale fraction Rees chart. -/
theorem toOriginalScaleOpen_range :
    (toOriginalScaleOpen W s b3 b4 b6 h3 h4 h6).range = scaleReesChart W s := by
  let f := toOriginalScaleOpen W s b3 b4 b6 h3 h4 h6
  let A := WeierstrassIntegralChart.Coordinate W 2
  let d : OriginalScaleOpen W s := IsLocalization.Away.invSelf (algebraMap R A s)
  have hr (i : Fin 3) (hi : i = 0 ∨ i = 1) :
      algebraMap A (OriginalScaleOpen W s) (WeierstrassIntegralChart.coord W 2 i) * d ∈
        scaleReesChart W s := by
    change _ ∈ BlowupFractionChart.chart (modificationCenter W s) (algebraMap R A s)
    rw [modificationCenter, BlowupFractionChart.chart_span]
    apply Algebra.subset_adjoin
    refine ⟨WeierstrassIntegralChart.coord W 2 i, ?_, rfl⟩
    rcases hi with rfl | rfl <;> simp
  apply le_antisymm
  · apply range_le_of_coordinates
    · rw [toOriginalScaleOpen, fractionMap_x]
      change d * algebraMap A (OriginalScaleOpen W s)
        (WeierstrassIntegralChart.coord W 2 0) ∈ scaleReesChart W s
      rw [mul_comm]
      exact hr 0 (Or.inl rfl)
    · rw [toOriginalScaleOpen, fractionMap_y]
      change d * algebraMap A (OriginalScaleOpen W s)
        (WeierstrassIntegralChart.coord W 2 1) ∈ scaleReesChart W s
      rw [mul_comm]
      exact hr 1 (Or.inr rfl)
  · intro z hz
    change z ∈ BlowupFractionChart.chart (modificationCenter W s) (algebraMap R A s) at hz
    rw [modificationCenter, BlowupFractionChart.chart_span] at hz
    induction hz using Algebra.adjoin_induction with
    | mem z hz =>
      rcases hz with ⟨a, ha, rfl⟩
      rcases Set.mem_insert_iff.mp ha with rfl | ha
      · change algebraMap A (OriginalScaleOpen W s) (algebraMap R A s) * d ∈ f.range
        have he : algebraMap A (OriginalScaleOpen W s) (algebraMap R A s) * d = 1 :=
          IsLocalization.Away.mul_invSelf _
        rw [he]
        exact f.range.one_mem
      · rcases Set.mem_insert_iff.mp ha with rfl | ha
        · refine ⟨x W s b3 b4 b6, ?_⟩
          change f (x W s b3 b4 b6) = _
          dsimp only [f]
          rw [toOriginalScaleOpen, fractionMap_x]
          exact mul_comm _ _
        · have ha' := Set.mem_singleton_iff.mp ha
          subst a
          refine ⟨y W s b3 b4 b6, ?_⟩
          change f (y W s b3 b4 b6) = _
          dsimp only [f]
          rw [toOriginalScaleOpen, fractionMap_y]
          exact mul_comm _ _
    | algebraMap a =>
      refine ⟨fromOriginal W s b3 b4 b6 h3 h4 h6 a, ?_⟩
      exact congrArg (fun k : A →ₐ[R] OriginalScaleOpen W s => k a)
        (toOriginalScaleOpen_fromOriginal W s b3 b4 b6 h3 h4 h6)
    | add a b ha hb ih ih' => exact f.range.add_mem ih ih'
    | mul a b ha hb ih ih' => exact f.range.mul_mem ih ih'

/-- The actual divided algebra is isomorphic to the original Rees fraction algebra. -/
def scaleReesChartEquiv (hs : IsRegular s) :
    Coordinate W s b3 b4 b6 ≃ₐ[R] scaleReesChart W s :=
  (AlgEquiv.ofInjective (toOriginalScaleOpen W s b3 b4 b6 h3 h4 h6)
    (toOriginalScaleOpen_injective W s b3 b4 b6 h3 h4 h6 hs)).trans
      (Subalgebra.equivOfEq _ _ (toOriginalScaleOpen_range W s b3 b4 b6 h3 h4 h6))

/-- The Rees comparison preserves the original contraction on every original function. -/
theorem scaleReesChartEquiv_fromOriginal (hs : IsRegular s)
    (a : WeierstrassIntegralChart.Coordinate W 2) :
    (scaleReesChartEquiv W s b3 b4 b6 h3 h4 h6 hs
      (fromOriginal W s b3 b4 b6 h3 h4 h6 a) : OriginalScaleOpen W s) =
        algebraMap (WeierstrassIntegralChart.Coordinate W 2) (OriginalScaleOpen W s) a :=
  congrArg (fun k : WeierstrassIntegralChart.Coordinate W 2 →ₐ[R] OriginalScaleOpen W s => k a)
    (toOriginalScaleOpen_fromOriginal W s b3 b4 b6 h3 h4 h6)

end FLT.Mazur.WeierstrassDilatation
