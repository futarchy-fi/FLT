/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.GrassmannianChartChangeDeterminant

/-!
# Coordinate transitions preserve the full quotient relation

A second decomposition of the ambient module gives transition coordinates by
inverting its quotient basis. The resulting graph kernel is exactly the original
relation transported along the ambient decomposition, not merely a pointwise invariant.
-/

@[expose] public noncomputable section
namespace FLT.Mazur.GrassmannianChart
variable {S : Type*} [CommRing S] {V W : Type*}
  [AddCommGroup V] [Module S V] [AddCommGroup W] [Module S W] {d : ℕ}

/-- The selected basis change for an alternate ambient decomposition. -/
def transitionBasis (A : V →ₗ[S] (Fin d → S))
    (e : ((Fin d → S) × W) ≃ₗ[S] ((Fin d → S) × V)) :=
  chartChangeMap A (e.toLinearMap.comp (LinearMap.inl S (Fin d → S) W))

/-- The invertible change of quotient basis on an overlap. -/
def transitionBasisEquiv (A : V →ₗ[S] (Fin d → S))
    (e : ((Fin d → S) × W) ≃ₗ[S] ((Fin d → S) × V))
    (h : Function.Bijective (transitionBasis A e)) : (Fin d → S) ≃ₗ[S] (Fin d → S) :=
  LinearEquiv.ofBijective _ h

/-- Complementary coordinates in the second quotient basis. -/
def chartTransition (A : V →ₗ[S] (Fin d → S))
    (e : ((Fin d → S) × W) ≃ₗ[S] ((Fin d → S) × V))
    (h : Function.Bijective (transitionBasis A e)) : W →ₗ[S] (Fin d → S) :=
  (transitionBasisEquiv A e h).symm.toLinearMap.comp
    ((splitChartEvaluation A).comp (e.toLinearMap.comp (LinearMap.inr S (Fin d → S) W)))

/-- Transition evaluation is the original evaluation expressed in the new quotient basis. -/
theorem chartTransition_factor (A : V →ₗ[S] (Fin d → S))
    (e : ((Fin d → S) × W) ≃ₗ[S] ((Fin d → S) × V))
    (h : Function.Bijective (transitionBasis A e)) :
    (transitionBasisEquiv A e h).toLinearMap.comp (splitChartEvaluation (chartTransition A e h)) =
      (splitChartEvaluation A).comp e.toLinearMap := by
  apply LinearMap.ext
  intro x
  apply funext
  intro i
  change transitionBasisEquiv A e h
    (x.1 + (transitionBasisEquiv A e h).symm (splitChartEvaluation A (e (0, x.2)))) i = _
  rw [map_add, LinearEquiv.apply_symm_apply]
  change (splitChartEvaluation A (e (x.1, 0)) + splitChartEvaluation A (e (0, x.2))) i = _
  rw [← map_add, ← map_add]
  simp only [Prod.mk_add_mk, add_zero, zero_add, Prod.eta, LinearMap.comp_apply,
    LinearEquiv.coe_coe]

/-- The transition preserves every ambient relation. -/
theorem chartTransition_kernel (A : V →ₗ[S] (Fin d → S))
    (e : ((Fin d → S) × W) ≃ₗ[S] ((Fin d → S) × V))
    (h : Function.Bijective (transitionBasis A e)) :
    (splitChartEvaluation (chartTransition A e h)).ker =
      (splitChartEvaluation A).ker.comap e.toLinearMap := by
  rw [← LinearEquiv.ker_comp (transitionBasisEquiv A e h), chartTransition_factor]
  rfl

/-- Any normalized coordinates with this evaluation factorization are the transition. -/
theorem chartTransition_unique (A : V →ₗ[S] (Fin d → S))
    (e : ((Fin d → S) × W) ≃ₗ[S] ((Fin d → S) × V))
    (h : Function.Bijective (transitionBasis A e)) (B : W →ₗ[S] (Fin d → S))
    (hB : (transitionBasis A e).comp (splitChartEvaluation B) =
      (splitChartEvaluation A).comp e.toLinearMap) : chartTransition A e h = B := by
  ext y i
  have hy := LinearMap.congr_fun hB (0, y)
  have he : transitionBasisEquiv A e h (B y) = splitChartEvaluation A (e (0, y)) := by
    change transitionBasis A e (0 + B y) = splitChartEvaluation A (e (0, y)) at hy
    change transitionBasis A e (B y) = _
    simpa only [zero_add] using hy
  change ((transitionBasisEquiv A e h).symm (splitChartEvaluation A (e (0, y)))) i = B y i
  rw [← he, LinearEquiv.symm_apply_apply]

end FLT.Mazur.GrassmannianChart
