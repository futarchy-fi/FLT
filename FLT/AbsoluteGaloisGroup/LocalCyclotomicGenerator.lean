/-
Copyright (c) 2026 Kelvin Santos. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kelvin Santos
-/
module

public import FLT.AbsoluteGaloisGroup.LocalCyclotomicSurjectivity
public import FLT.AbsoluteGaloisGroup.LocalCyclotomicTame

/-!
# An inertia element generating the cyclotomic and tame images
-/

@[expose] public noncomputable section

namespace LocalCyclotomic

variable (p : ℕ) [Fact p.Prime]

/-- A single local inertia element generates all mod-p cyclotomic values. -/
theorem exists_inertiaCharacter_generator :
    ∃ t : localInertiaGroup (rationalPlace p),
      ∀ a : (ZMod p)ˣ, a ∈ Subgroup.zpowers (inertiaCharacter p t) := by
  obtain ⟨a, ha⟩ := IsCyclic.exists_generator (α := (ZMod p)ˣ)
  obtain ⟨t, ht⟩ := inertiaCharacter_surjective p a
  exact ⟨t, ht ▸ ha⟩

/-- The same inertia element generates both the cyclotomic and tame values. -/
theorem exists_simultaneous_generator :
    ∃ t : localInertiaGroup (rationalPlace p),
      (∀ a : (ZMod p)ˣ, a ∈ Subgroup.zpowers (inertiaCharacter p t)) ∧
      ∀ a : (IsLocalRing.ResidueField ((rationalPlace p).adicCompletionIntegers ℚ))ˣ,
        a ∈ Subgroup.zpowers (tameCharacter (rationalPlace p) t) := by
  obtain ⟨t, ht⟩ := exists_inertiaCharacter_generator p
  refine ⟨t, ht, fun a ↦ ?_⟩
  let e := Units.mapEquiv (residueEquiv p).toMulEquiv
  obtain ⟨n, hn⟩ := Subgroup.mem_zpowers_iff.mp (ht (e a))
  apply Subgroup.mem_zpowers_iff.mpr
  refine ⟨n, e.injective ?_⟩
  rw [map_zpow]
  have he := DFunLike.congr_fun (tameCharacter_eq_inertiaCharacter p) t
  change e (tameCharacter (rationalPlace p) t) = inertiaCharacter p t at he
  rwa [he]

end LocalCyclotomic
