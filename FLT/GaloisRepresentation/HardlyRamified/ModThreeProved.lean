/-
Copyright (c) 2026 krandder. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: krandder
-/
module

public import FLT.Assembly.PrimePowerSortingProof

/-!
# Unconditional mod-three quotient from integral sorting

The proved sorting theorem supplies the invariant quotient. Its kernel rules
out irreducibility; no compatible family or admitted mod-three theorem is used.
-/

@[expose] public noncomputable section

namespace GaloisRepresentation.IsHardlyRamified

variable {k : Type*} [Finite k] [Field k] [Algebra ℤ_[3] k]
  [TopologicalSpace k] [DiscreteTopology k]
  {V : Type*} [AddCommGroup V] [Module k V] [Module.Finite k V] [Module.Free k V]
  (hV : Module.rank k V = 2) {ρ : GaloisRep ℚ k V}

/-- Proved integral sorting gives the original coefficient-linear trivial quotient. -/
theorem mod_three_from_sorting
    (hρ : IsHardlyRamified (show Odd 3 by decide) hV ρ) :
    ∃ (π : V →ₗ[k] k) (_ : Function.Surjective π),
      ∀ (g : Field.absoluteGaloisGroup ℚ) (v : V), π (ρ g v) = π v :=
  hρ.mod_three_of_sortedExtensionExists
    (ThreeAdicPlan.sortedExtensionExists_of_primePowerSorting
      ThreeAdicPlan.primePowerSortedExtensionExists) V hV

/-- No rank-two mod-three hardly ramified representation is irreducible. -/
theorem not_isIrreducible_three
    (hρ : IsHardlyRamified (show Odd 3 by decide) hV ρ) : ¬ ρ.IsIrreducible := by
  obtain ⟨π, hπ, hinv⟩ := mod_three_from_sorting hV hρ
  intro hirr
  let : ρ.toRepresentation.IsIrreducible := hirr
  let W : Subrepresentation ρ.toRepresentation :=
    { toSubmodule := LinearMap.ker π
      apply_mem_toSubmodule := by
        intro g v hv
        change π (ρ g v) = 0
        exact (hinv g v).trans hv }
  rcases eq_bot_or_eq_top W with hw | hw
  · have hinj : Function.Injective π := LinearMap.ker_eq_bot.mp
      (congrArg Subrepresentation.toSubmodule hw)
    have hdim := LinearMap.finrank_le_finrank_of_injective hinj
    have htwo : Module.finrank k V = 2 := Module.finrank_eq_of_rank_eq hV
    rw [htwo, Module.finrank_self] at hdim
    omega
  · obtain ⟨v, hv⟩ := hπ 1
    have hm : v ∈ W := by rw [hw]; trivial
    change π v = 0 at hm
    exact one_ne_zero (hv.symm.trans hm)

end GaloisRepresentation.IsHardlyRamified
