/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.GrassmannianChartTransition

/-!
# Grassmannian chart transitions satisfy the cocycle

Successive changes of quotient basis multiply, and normalized coordinates agree
on triple overlaps. The overlap condition for the composite is constructed from
the two successive overlap conditions.
-/

@[expose] public noncomputable section
namespace FLT.Mazur.GrassmannianChart
variable {S : Type*} [CommRing S] {V W U : Type*}
  [AddCommGroup V] [Module S V] [AddCommGroup W] [Module S W]
  [AddCommGroup U] [Module S U] {d : ℕ}

/-- Successive quotient basis changes multiply as actual linear maps. -/
theorem transitionBasis_comp (A : V →ₗ[S] (Fin d → S))
    (e : ((Fin d → S) × W) ≃ₗ[S] ((Fin d → S) × V))
    (f : ((Fin d → S) × U) ≃ₗ[S] ((Fin d → S) × W))
    (h : Function.Bijective (transitionBasis A e)) :
    transitionBasis A (f.trans e) =
      (transitionBasis A e).comp (transitionBasis (chartTransition A e h) f) := by
  apply LinearMap.ext
  intro x
  exact (LinearMap.congr_fun (chartTransition_factor A e h) (f (x, 0))).symm

/-- A point in two successive overlaps also lies in the composite overlap. -/
theorem transitionBasis_comp_bijective (A : V →ₗ[S] (Fin d → S))
    (e : ((Fin d → S) × W) ≃ₗ[S] ((Fin d → S) × V))
    (f : ((Fin d → S) × U) ≃ₗ[S] ((Fin d → S) × W))
    (h : Function.Bijective (transitionBasis A e))
    (k : Function.Bijective (transitionBasis (chartTransition A e h) f)) :
    Function.Bijective (transitionBasis A (f.trans e)) := by
  rw [transitionBasis_comp A e f h]
  exact h.comp k

/-- The normalized transition coordinates satisfy the triple-overlap cocycle. -/
theorem chartTransition_cocycle (A : V →ₗ[S] (Fin d → S))
    (e : ((Fin d → S) × W) ≃ₗ[S] ((Fin d → S) × V))
    (f : ((Fin d → S) × U) ≃ₗ[S] ((Fin d → S) × W))
    (h : Function.Bijective (transitionBasis A e))
    (k : Function.Bijective (transitionBasis (chartTransition A e h) f)) :
    chartTransition A (f.trans e) (transitionBasis_comp_bijective A e f h k) =
      chartTransition (chartTransition A e h) f k := by
  apply chartTransition_unique
  rw [transitionBasis_comp A e f h, LinearMap.comp_assoc]
  change (transitionBasisEquiv A e h).toLinearMap.comp
    ((transitionBasisEquiv (chartTransition A e h) f k).toLinearMap.comp
      (splitChartEvaluation (chartTransition (chartTransition A e h) f k))) = _
  rw [chartTransition_factor, ← LinearMap.comp_assoc, chartTransition_factor]
  rfl

/-- The identity ambient decomposition is always in the overlap. -/
theorem transitionBasis_refl (A : V →ₗ[S] (Fin d → S)) :
    transitionBasis A (LinearEquiv.refl S _) = LinearMap.id := by
  exact splitChartEvaluation_section A

/-- Changing to the same ambient decomposition leaves the coordinates unchanged. -/
theorem chartTransition_refl (A : V →ₗ[S] (Fin d → S))
    (h : Function.Bijective (transitionBasis A (LinearEquiv.refl S _))) :
    chartTransition A (LinearEquiv.refl S _) h = A := by
  apply chartTransition_unique
  rw [transitionBasis_refl]
  rfl

end FLT.Mazur.GrassmannianChart
