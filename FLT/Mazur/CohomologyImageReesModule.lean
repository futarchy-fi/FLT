/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.IdealAdicCohomologyScalars
public import Mathlib.Algebra.DirectSum.Module

/-!
# The Rees module of actual cohomology images

The direct sum of cohomology of the original ideal powers maps onto the
Rees module of their images. This constructs the comparison whose finite
generation must be proved geometrically; no stability is assumed.
-/

@[expose] public noncomputable section

set_option backward.isDefEq.respectTransparency false

open CategoryTheory AlgebraicGeometry
open FLT.Mazur.FCurve FLT.Mazur.GlobalIdealPower
open scoped DirectSum

universe u

namespace FLT.Mazur.IdealAdicQuotient

variable {X : Scheme.{u}} [IsLocallyNoetherian X]
  {R : Type u} [CommRing R] (ρ : R →+* Γ(X, ⊤))
  (I : X.IdealSheafData) (M : X.Modules) [M.IsFinitePresentation]
  (J : Ideal R)
  (hJ : ∀ (r : R), r ∈ J → ∀ U : X.affineOpens,
    X.presheaf.map U.1.leTop.op (ρ r) ∈ I.ideal U)
  (q : ℕ)

/-- The actual image Rees module, inside polynomial-valued cohomology. -/
def cohomologyRees : Submodule (reesAlgebra J) (PolynomialModule R (ModuleRingH ρ M q)) :=
  (cohomologyFiltration ρ I M J hJ q).submodule

/-- Rees membership means that each coefficient lifts through its original power inclusion. -/
lemma mem_cohomologyRees (p : PolynomialModule R (ModuleRingH ρ M q)) :
    p ∈ cohomologyRees ρ I M J hJ q ↔
      ∀ n, ∃ y, moduleHMap (inclusion (I ^ n) M) q y = p.coeff n := Iff.rfl

/-- The source retains cohomology of every actual ideal power, with finite degree support. -/
abbrev PowerCohomologySum := ⨁ n : ℕ, ModuleRingH ρ (power I n M) q

/-- The original inclusions assemble into a map of the full direct sums. -/
def powerCohomologyComparison :
    PowerCohomologySum ρ I M q →ₗ[R] PolynomialModule R (ModuleRingH ρ M q) :=
  DirectSum.toModule R ℕ _ (fun n ↦ (PolynomialModule.lsingle R n).comp
    ((moduleRingHFunctor ρ q).map (inclusion (I ^ n) M)).hom)

omit [IsLocallyNoetherian X] [M.IsFinitePresentation] in
/-- A homogeneous class is sent through its original power inclusion. -/
lemma powerCohomologyComparison_of (n : ℕ) (x : ModuleRingH ρ (power I n M) q) :
    powerCohomologyComparison ρ I M q (DirectSum.lof R ℕ _ n x) =
      PolynomialModule.single (M := ModuleRingH ρ M q) R n
        (((moduleRingHFunctor ρ q).map (inclusion (I ^ n) M)).hom x) := by
  simp only [powerCohomologyComparison, DirectSum.toModule_lof, LinearMap.comp_apply]
  rfl

/-- The range is exactly the Rees module of the actual cohomology images. -/
theorem powerCohomologyComparison_range :
    LinearMap.range (powerCohomologyComparison ρ I M q) =
      (cohomologyRees ρ I M J hJ q).restrictScalars R := by
  classical
  apply le_antisymm
  · rintro _ ⟨x, rfl⟩
    induction x using DirectSum.induction_on with
    | zero => exact (cohomologyRees ρ I M J hJ q).zero_mem
    | add x y hx hy =>
      rw [map_add]
      exact (cohomologyRees ρ I M J hJ q).add_mem hx hy
    | of n x =>
      change powerCohomologyComparison ρ I M q (DirectSum.lof R ℕ _ n x) ∈ _
      rw [powerCohomologyComparison_of]
      intro k
      by_cases h : n = k
      · subst k
        simp only [PolynomialModule.coeff_single, Finsupp.single_eq_same]
        exact ⟨x, rfl⟩
      · simp only [PolynomialModule.coeff_single, Finsupp.single_apply, ite_eq_right h]
        exact (cohomologyImage ρ I M q k).zero_mem
  · intro p hp
    rw [← p.ofCoeff_coeff, ← p.coeff.sum_single, PolynomialModule.ofCoeff_finsuppSum]
    apply Submodule.sum_mem
    intro n _
    obtain ⟨x, hx⟩ := hp n
    refine ⟨DirectSum.lof R ℕ _ n x, ?_⟩
    rw [powerCohomologyComparison_of]
    exact congrArg (PolynomialModule.single (M := ModuleRingH ρ M q) R n) hx

end FLT.Mazur.IdealAdicQuotient
