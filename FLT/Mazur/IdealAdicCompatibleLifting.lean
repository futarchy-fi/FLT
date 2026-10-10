/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.IdealAdicCohomologyRestriction
public import FLT.Mazur.IdealAdicCohomology
public import FLT.Mazur.SurjectiveTowerLifting

/-!
# Compatible infinitesimal lifts of cohomology classes

Surjective adjacent reductions extend a specified finite-level class to
an actual compatible family. Graded H1 vanishing supplies this for H0.
-/

@[expose] public noncomputable section

set_option backward.isDefEq.respectTransparency false

open CategoryTheory AlgebraicGeometry
open FLT.Mazur.FCurve

universe u

namespace FLT.Mazur.IdealAdicQuotient

variable {X : Scheme.{u}} [IsLocallyNoetherian X]
  {R : Type u} [CommRing R] (ρ : R →+* Γ(X, ⊤))
  (I : X.IdealSheafData) (M : X.Modules) [M.IsFinitePresentation]

/-- Surjective adjacent reductions extend every finite-level class to a compatible family. -/
theorem compatibleCohomology_eval_surjective (q : ℕ)
    (h : ∀ n, Function.Surjective (moduleHMap (reduction I M (Nat.le_succ n)) q))
    (n : ℕ) : Function.Surjective
      (fun x : compatibleCohomology ρ I M q ↦ x.val n) := by
  intro x
  obtain ⟨y, hy, hyn⟩ := SurjectiveTowerLifting.exists_compatible
    (F := fun k ↦ ModuleRingH ρ (quotient I M k) q)
    (fun hab ↦ moduleHMap (reduction I M hab) q) h
    (fun a z ↦ by rw [reduction_refl, moduleHMap_id]; rfl)
    (fun hab hbc z ↦ by
      rw [← LinearMap.comp_apply, ← moduleHMap_comp, reduction_trans]) n x
  exact ⟨⟨y, hy⟩, hyn⟩

/-- Vanishing of the actual graded H1 lifts every infinitesimal H0 class compatibly. -/
theorem compatibleH0_eval_surjective
    (h : ∀ k, Subsingleton (ModuleH (graded I M k) 1)) (n : ℕ) :
    Function.Surjective (fun x : compatibleCohomology ρ I M 0 ↦ x.val n) :=
  compatibleCohomology_eval_surjective ρ I M 0
    (fun k ↦ reduction_h0_surjective I M k (h k)) n

/-- Algebraization of compatible classes and graded H1 vanishing lift finite-level classes. -/
theorem projection_h0_surjective_of_reconstruction
    (hc : Function.Surjective (cohomologyRestriction ρ I M 0))
    (h : ∀ k, Subsingleton (ModuleH (graded I M k) 1)) (n : ℕ) :
    Function.Surjective (moduleHMap (projection I M n) 0) := by
  intro x
  obtain ⟨y, hy⟩ := compatibleH0_eval_surjective ρ I M h n x
  obtain ⟨z, hz⟩ := hc y
  exact ⟨z, (congrArg (fun w ↦ w.val n) hz).trans hy⟩

end FLT.Mazur.IdealAdicQuotient
