/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.IdealAdicImageCompletion

/-!
# The range of the actual formal comparison

Under cofinality, the only obstruction is coordinatewise liftability from the
original cohomology. Eventual liftability of transition images suffices.
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

/-- The finite descended comparison has exactly the range of original restriction. -/
lemma mem_range_imageQuotientComparison_iff (q n : ℕ)
    (y : ModuleRingH ρ (quotient I M n) q) :
    y ∈ LinearMap.range (imageQuotientComparison ρ I M q n) ↔
      ∃ x : ModuleRingH ρ M q, moduleHMap (projection I M n) q x = y := by
  constructor
  · rintro ⟨z, hz⟩
    obtain ⟨x, rfl⟩ := Submodule.Quotient.mk_surjective _ z
    exact ⟨x, hz⟩
  · rintro ⟨x, rfl⟩
    exact ⟨Submodule.Quotient.mk x, rfl⟩

/-- Cofinality identifies the formal image with the coordinatewise restriction images. -/
theorem mem_range_formalComparison_iff (q : ℕ)
    (h : ∀ n, ∃ m, n ≤ m ∧ cohomologyImage ρ I M q m ≤
      J ^ n • (⊤ : Submodule R (ModuleRingH ρ M q)))
    (y : compatibleCohomology ρ I M q) :
    y ∈ LinearMap.range (formalComparison ρ I M J hJ q) ↔
      ∀ n, ∃ x : ModuleRingH ρ M q, moduleHMap (projection I M n) q x = y.val n := by
  have hr : y ∈ LinearMap.range (formalComparison ρ I M J hJ q) ↔
      y ∈ LinearMap.range (compatibleImageComparison ρ I M q) := by
    constructor
    · rintro ⟨x, rfl⟩
      exact ⟨completionToImages ρ I M J hJ q x,
        compatibleImageComparison_completionToImages ρ I M J hJ q x⟩
    · rintro ⟨z, rfl⟩
      obtain ⟨x, rfl⟩ := completionToImages_surjective_of_cofinal ρ I M J hJ q h z
      exact ⟨x, (compatibleImageComparison_completionToImages ρ I M J hJ q x).symm⟩
  rw [hr, mem_range_compatibleImageComparison_iff]
  exact forall_congr' fun n ↦ mem_range_imageQuotientComparison_iff ρ I M q n (y.val n)

/-- It suffices that every sufficiently deep quotient class becomes liftable at each level. -/
theorem formalComparison_surjective_of_eventual_lifts (q : ℕ)
    (h : ∀ n, ∃ m, n ≤ m ∧ cohomologyImage ρ I M q m ≤
      J ^ n • (⊤ : Submodule R (ModuleRingH ρ M q)))
    (hlift : ∀ n, ∃ m, ∃ hnm : n ≤ m,
      ∀ z : ModuleRingH ρ (quotient I M m) q,
        ∃ x : ModuleRingH ρ M q,
          moduleHMap (projection I M n) q x = moduleHMap (reduction I M hnm) q z) :
    Function.Surjective (formalComparison ρ I M J hJ q) := by
  intro y
  apply (mem_range_formalComparison_iff ρ I M J hJ q h y).mpr
  intro n
  obtain ⟨m, hnm, hm⟩ := hlift n
  obtain ⟨x, hx⟩ := hm (y.val m)
  exact ⟨x, hx.trans (y.property n m hnm)⟩

end FLT.Mazur.IdealAdicQuotient
