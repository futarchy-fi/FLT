/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.IdealAdicCompatibleLifting

/-!
# Finite-level algebraization without a complete base

A completed cohomology class has an ordinary cohomology representative at
any specified finite level. Thus formal surjectivity and compatible lifting
already give finite-level lifts; base-ring completeness is unnecessary.
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
  (J : Ideal R)
  (hJ : ∀ (r : R), r ∈ J → ∀ U : X.affineOpens,
    X.presheaf.map U.1.leTop.op (ρ r) ∈ I.ideal U)

/-- Every coordinate of a formal class is the restriction of an ordinary class. -/
theorem formalComparison_coordinate_lift (q n : ℕ)
    (z : AdicCompletion J (ModuleRingH ρ M q)) :
    ∃ x : ModuleRingH ρ M q, moduleHMap (projection I M n) q x =
      (formalComparison ρ I M J hJ q z).val n := by
  obtain ⟨x, hx⟩ := Submodule.Quotient.mk_surjective
    (J ^ n • (⊤ : Submodule R (ModuleRingH ρ M q))) (z.val n)
  refine ⟨x, ?_⟩
  rw [formalComparison_eval]
  change moduleHMap (projection I M n) q x = adicQuotientComparison ρ I M J hJ q n (z.val n)
  rw [← hx, adicQuotientComparison_mk]

/-- Formal surjectivity and surjective transitions give actual lifts at every finite level. -/
theorem projection_surjective_of_formal (q : ℕ)
    (hf : Function.Surjective (formalComparison ρ I M J hJ q))
    (hr : ∀ k, Function.Surjective (moduleHMap (reduction I M (Nat.le_succ k)) q))
    (n : ℕ) : Function.Surjective (moduleHMap (projection I M n) q) := by
  intro x
  obtain ⟨y, hy⟩ := compatibleCohomology_eval_surjective ρ I M q hr n x
  obtain ⟨z, hz⟩ := hf y
  obtain ⟨w, hw⟩ := formalComparison_coordinate_lift ρ I M J hJ q n z
  exact ⟨w, hw.trans ((congrArg (fun t ↦ t.val n) hz).trans hy)⟩

end FLT.Mazur.IdealAdicQuotient
