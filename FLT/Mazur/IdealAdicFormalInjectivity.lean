/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.IdealAdicFormalComparison

/-!
# Injectivity of the formal comparison from cofinal image filtrations

A completed class vanishing on every coefficient quotient has a representative
in every cohomology image. Reverse adic containment makes all its evaluations zero.
-/

@[expose] public noncomputable section

set_option backward.defeqAttrib.useBackward true
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

/-- Cofinality of the original image filtration proves injectivity of the actual comparison. -/
theorem formalComparison_injective_of_cofinal (q : ℕ)
    (h : ∀ n, ∃ m, n ≤ m ∧ cohomologyImage ρ I M q m ≤
      J ^ n • (⊤ : Submodule R (ModuleRingH ρ M q))) :
    Function.Injective (formalComparison ρ I M J hJ q) := by
  rw [← LinearMap.ker_eq_bot, LinearMap.ker_eq_bot']
  intro x hx
  apply AdicCompletion.ext
  intro n
  change x.val n = 0
  obtain ⟨m, hnm, hm⟩ := h n
  obtain ⟨y, hy⟩ := Submodule.Quotient.mk_surjective _ (x.val m)
  have hy0 : moduleHMap (projection I M m) q y = 0 := by
    have he := congrArg (fun z : compatibleCohomology ρ I M q ↦ z.val m) hx
    change adicQuotientComparison ρ I M J hJ q m (x.val m) = 0 at he
    rw [← hy, adicQuotientComparison_mk] at he
    exact he
  have hyn := hm ((mem_cohomologyImage_iff ρ I M q m y).mpr hy0)
  have he := x.property hnm
  rw [← hy] at he
  change Submodule.Quotient.mk y = x.val n at he
  rw [← he]
  rw [Submodule.Quotient.mk_eq_zero]
  exact hyn

end FLT.Mazur.IdealAdicQuotient
