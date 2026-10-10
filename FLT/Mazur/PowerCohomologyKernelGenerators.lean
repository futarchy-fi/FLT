/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.PowerCohomologyReesQuotient

/-!
# Bounded-degree generators for the power-cohomology kernel

Finite generation of the actual Rees kernel can be witnessed by homogeneous
classes of bounded degree. Each generator still lies in an original inclusion kernel.
-/

@[expose] public noncomputable section

set_option backward.defeqAttrib.useBackward true
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
  (hJ : ∀ r : R, r ∈ J → ∀ U : X.affineOpens,
    X.presheaf.map U.1.leTop.op (ρ r) ∈ I.ideal U) (q : ℕ)

/-- An original homogeneous inclusion-kernel class lies in the full Rees kernel. -/
lemma powerReesComparison_ker_of (n : ℕ) (x : ModuleRingH ρ (power I n M) q)
    (hx : moduleHMap (inclusion (I ^ n) M) q x = 0) :
    let _ := powerReesModule ρ I M J hJ q
    (DirectSum.lof R ℕ _ n x : PowerCohomologySum ρ I M q) ∈
      LinearMap.ker (powerReesComparison ρ I M J hJ q) := by
  let _ := powerReesModule ρ I M J hJ q
  change powerCohomologyComparison ρ I M q (DirectSum.lof R ℕ _ n x) = 0
  rw [powerCohomologyComparison_of]
  change PolynomialModule.single (M := ModuleRingH ρ M q) R n
    (moduleHMap (inclusion (I ^ n) M) q x) = 0
  rw [hx, PolynomialModule.single_zero]

/-- Finite generation yields a single bound for the homogeneous inclusion-kernel generators. -/
theorem powerReesComparison_ker_bounded_generators :
    let _ := powerReesModule ρ I M J hJ q
    (LinearMap.ker (powerReesComparison ρ I M J hJ q)).FG →
      ∃ c : ℕ, LinearMap.ker (powerReesComparison ρ I M J hJ q) =
        Submodule.span (reesAlgebra J)
          {x | ∃ n ≤ c, ∃ z : ModuleRingH ρ (power I n M) q,
            moduleHMap (inclusion (I ^ n) M) q z = 0 ∧
              DirectSum.lof R ℕ _ n z = x} := by
  classical
  let _ := powerReesModule ρ I M J hJ q
  dsimp only
  rintro ⟨s, hs⟩
  let c := s.sup (fun x ↦ x.support.sup id)
  refine ⟨c, le_antisymm ?_ ?_⟩
  · rw [← hs]
    apply Submodule.span_le.mpr
    intro x hx
    have hxK : x ∈ LinearMap.ker (powerReesComparison ρ I M J hJ q) := by
      rw [← hs]
      exact Submodule.subset_span hx
    have hk := (mem_powerReesComparison_ker ρ I M J hJ q x).mp hxK
    rw [← DirectSum.sum_support_of x]
    apply Submodule.sum_mem
    intro n hn
    apply Submodule.subset_span
    refine ⟨n, ?_, x n, hk n, rfl⟩
    exact (Finset.le_sup (f := id) hn).trans (Finset.le_sup (f := fun y ↦ y.support.sup id) hx)
  · apply Submodule.span_le.mpr
    rintro x ⟨n, _, z, hz, rfl⟩
    exact powerReesComparison_ker_of ρ I M J hJ q n z hz

end FLT.Mazur.IdealAdicQuotient
