/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.PowerCohomologyKernelReduction

/-!
# Eventual vanishing of power-inclusion kernels

Finite generation of the genuine Rees kernel gives bounded-degree homogeneous
generators. The original transition kills all their sufficiently high Rees multiples.
-/

@[expose] public noncomputable section

set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false

open CategoryTheory AlgebraicGeometry
open FLT.Mazur.FCurve FLT.Mazur.GlobalIdealPower
open FLT.Mazur.GlobalIdealPowerCompatibility
open scoped DirectSum

universe u

namespace FLT.Mazur.IdealAdicQuotient

variable {X : Scheme.{u}} [IsLocallyNoetherian X]
  {R : Type u} [CommRing R] (ρ : R →+* Γ(X, ⊤))
  (I : X.IdealSheafData) (M : X.Modules) [M.IsFinitePresentation]
  (J : Ideal R)
  (hJ : ∀ r : R, r ∈ J → ∀ U : X.affineOpens,
    X.presheaf.map U.1.leTop.op (ρ r) ∈ I.ideal U) (q : ℕ)

/-- A finite genuine Rees kernel has a uniform transition-vanishing bound. -/
theorem power_kernel_transition_vanishing_of_fg :
    let _ := powerReesModule ρ I M J hJ q
    (LinearMap.ker (powerReesComparison ρ I M J hJ q)).FG →
      ∃ c : ℕ, ∀ b d : ℕ, ∀ hbd : b ≤ d, b + c ≤ d →
        ∀ x : ModuleRingH ρ (power I d M) q,
          moduleHMap (inclusion (I ^ d) M) q x = 0 →
            moduleHMap (transition I M hbd) q x = 0 := by
  let _ := powerReesModule ρ I M J hJ q
  dsimp only
  intro hfg
  obtain ⟨c, hc⟩ := powerReesComparison_ker_bounded_generators ρ I M J hJ q hfg
  refine ⟨c, fun b d hbd hd x hx ↦ ?_⟩
  have hm := powerReesComparison_ker_of ρ I M J hJ q d x hx
  rw [hc] at hm
  have hspan : ∀ p : reesAlgebra J,
      powerTransitionComponent ρ I M q hbd (p • DirectSum.lof R ℕ _ d x) = 0 := by
    refine Submodule.span_induction
      (p := fun z _ ↦ ∀ p : reesAlgebra J,
        powerTransitionComponent ρ I M q hbd (p • z) = 0) ?_ ?_ ?_ ?_ hm
    · rintro z ⟨n, hn, z, hz, rfl⟩ p
      exact powerTransitionComponent_rees_kernel ρ I M J hJ q b d n hbd
        ((Nat.add_le_add_left hn b).trans hd) p z hz
    · intro p
      rw [smul_zero, map_zero]
    · intro z w _ _ hz hw p
      rw [smul_add, map_add, hz p, hw p, add_zero]
    · intro r z _ hz p
      rw [smul_smul]
      exact hz (p * r)
  have h := hspan 1
  rw [one_smul] at h
  rw [powerTransitionComponent_apply] at h
  simpa only [DirectSum.lof_eq_of, DirectSum.of_eq_same] using h

/-- Each target receives zero from a sufficiently deep actual inclusion kernel. -/
theorem power_kernel_eventually_zero_of_fg :
    let _ := powerReesModule ρ I M J hJ q
    (LinearMap.ker (powerReesComparison ρ I M J hJ q)).FG →
      ∀ n, ∃ m, ∃ hnm : n ≤ m,
        ∀ z : ModuleRingH ρ (power I m M) q,
          moduleHMap (inclusion (I ^ m) M) q z = 0 →
            moduleHMap (transition I M hnm) q z = 0 := by
  let _ := powerReesModule ρ I M J hJ q
  dsimp only
  intro hfg
  obtain ⟨c, hc⟩ := power_kernel_transition_vanishing_of_fg ρ I M J hJ q hfg
  intro n
  exact ⟨n + c, Nat.le_add_right n c, hc n (n + c) (Nat.le_add_right n c) le_rfl⟩

end FLT.Mazur.IdealAdicQuotient
