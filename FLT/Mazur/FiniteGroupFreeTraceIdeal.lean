/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.FiniteGroupBoundaryTrace
public import FLT.Mazur.FiniteGroupFreeOrbitSeparation

/-!
# Freeness makes the orbit-trace ideal the unit ideal

Summing the constructed identity separator proves that orbit traces generate
the unit ideal in the original source ring. Integrality of the fixed-ring
inclusion then proves the same statement with invariant coefficients.
-/

@[expose] public noncomputable section
open scoped BigOperators
namespace FLT.Mazur.FiniteGroupQuotient
variable (G : Type*) [Group G] [Fintype G]
  (A : Type*) [CommRing A] [MulSemiringAction G A]

/-- The ideal of source-linear combinations of orbit traces. -/
def orbitTraceIdeal : Ideal A :=
  Ideal.span (Set.range (fun a : A ↦ (orbitTrace G a).val))

/-- Summing an orbit combination gives a member of the actual trace ideal. -/
theorem sum_mem_orbitTraceIdeal {v : G → A} (hv : v ∈ orbitSpan G A) :
    ∑ g, v g ∈ orbitTraceIdeal G A := by
  induction hv using Submodule.span_induction with
  | mem v hv =>
    obtain ⟨a, rfl⟩ := hv
    exact Ideal.subset_span ⟨a, rfl⟩
  | zero => simpa only [Pi.zero_apply, Finset.sum_const_zero] using
      (orbitTraceIdeal G A).zero_mem
  | add v w _ _ hv hw =>
    simpa only [Pi.add_apply, Finset.sum_add_distrib] using
      (orbitTraceIdeal G A).add_mem hv hw
  | smul a v _ hv =>
    simpa only [Pi.smul_apply, smul_eq_mul, Finset.mul_sum] using
      (orbitTraceIdeal G A).mul_mem_left a hv

/-- Empty fixed subschemes produce a unit-ideal identity in the original source ring. -/
theorem orbitTraceIdeal_eq_top
    (hfree : ∀ g : G, g ≠ 1 → fixedPointIdeal G A g = ⊤) :
    orbitTraceIdeal G A = ⊤ := by
  obtain ⟨v, hv, hv₁, hv₀⟩ := exists_identity_orbit_combination G A hfree
  apply (Ideal.eq_top_iff_one _).mpr
  have hsum : ∑ g, v g = 1 := by
    rw [Fintype.sum_eq_single 1 (fun g hg ↦ hv₀ g hg), hv₁]
  exact hsum ▸ sum_mem_orbitTraceIdeal G A hv

/-- The ideal using invariant coefficients instead of arbitrary source coefficients. -/
def invariantTraceIdeal : Ideal (invariantRing G A) := Ideal.span (Set.range (orbitTrace G))

/-- Extension of the invariant trace ideal recovers the actual source trace ideal. -/
theorem invariantTraceIdeal_map :
    (invariantTraceIdeal G A).map (inclusion G A) = orbitTraceIdeal G A := by
  rw [invariantTraceIdeal, Ideal.map_span, ← Set.range_comp]
  rfl

/-- Integrality detects the unit ideal and supplies invariant trace coefficients. -/
theorem invariantTraceIdeal_eq_top
    (hfree : ∀ g : G, g ≠ 1 → fixedPointIdeal G A g = ⊤) :
    invariantTraceIdeal G A = ⊤ := by
  apply (Ideal.map_eq_top_iff (inclusion G A) (inclusion_injective G A)
    (inclusion_isIntegral G A)).mp
  rw [invariantTraceIdeal_map, orbitTraceIdeal_eq_top G A hfree]

end FLT.Mazur.FiniteGroupQuotient
