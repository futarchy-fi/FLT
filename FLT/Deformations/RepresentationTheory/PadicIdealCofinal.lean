/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import Mathlib.Analysis.SpecificLimits.Normed
public import Mathlib.NumberTheory.Padics.PadicIntegers
public import Mathlib.Topology.Algebra.Algebra

/-!
# Cofinality of p-power ideals in a p-adic algebra

Every open ideal contains a power of p, since these powers tend to zero.
No finiteness, freeness or local-ring hypothesis is needed for this direction.
-/

@[expose] public section

namespace PadicInt

variable (p : ℕ) [Fact p.Prime] (A : Type*) [CommRing A]
  [TopologicalSpace A] [Algebra ℤ_[p] A] [ContinuousSMul ℤ_[p] A]

/-- Powers of p tend to zero in any topological p-adic algebra. -/
theorem tendsto_algebra_pow_p :
    Filter.Tendsto (fun n : ℕ ↦ (p : A) ^ n) Filter.atTop (nhds 0) := by
  have hp : ‖(p : ℤ_[p])‖ < 1 := by
    rw [norm_p]
    exact inv_lt_one_of_one_lt₀ (by exact_mod_cast (Fact.out : p.Prime).one_lt)
  simpa only [Function.comp_def, map_pow, map_natCast, map_zero] using
    ((continuous_algebraMap ℤ_[p] A).tendsto 0).comp
      (tendsto_pow_atTop_nhds_zero_of_norm_lt_one hp)

/-- The principal p-power ideals are cofinal among the open ideals. -/
theorem exists_p_pow_le_of_isOpen (I : Ideal A) (hI : IsOpen (I : Set A)) :
    ∃ n : ℕ, Ideal.span {(p : A) ^ n} ≤ I := by
  have he : ∀ᶠ n : ℕ in Filter.atTop, (p : A) ^ n ∈ I :=
    (tendsto_algebra_pow_p p A) (hI.mem_nhds I.zero_mem)
  obtain ⟨n, hn⟩ := he.exists
  exact ⟨n, Ideal.span_le.mpr (by simpa only [Set.singleton_subset_iff, SetLike.mem_coe] using hn)⟩

end PadicInt
