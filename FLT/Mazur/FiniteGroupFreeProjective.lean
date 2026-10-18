/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.FiniteGroupTraceRetraction
public import Mathlib.Algebra.Module.Projective
public import Mathlib.RingTheory.Finiteness.Basic

/-!
# Finite projectivity of a free finite-group quotient

The identity orbit separator gives a finite dual generating system using
weighted traces. It splits a finite free module onto the original source ring.
No finite-type assumption or inverse of the group order is needed.
-/

@[expose] public noncomputable section
open scoped BigOperators
namespace FLT.Mazur.FiniteGroupQuotient
variable (G : Type*) [Group G] [Fintype G]
  {A : Type*} [CommRing A] [MulSemiringAction G A]
  (hfree : ∀ g : G, g ≠ 1 → fixedPointIdeal G A g = ⊤)

include hfree

/-- The original orbit separator produces a finite trace dual generating system. -/
theorem exists_trace_dual_generators :
    ∃ (s : Finset A) (a : A → A), ∀ x : A,
      ∑ b ∈ s, weightedTraceLinear G b x • a b = x := by
  classical
  obtain ⟨v, hv, hv₁, hv₀⟩ := exists_identity_orbit_combination G A hfree
  obtain ⟨c, hc⟩ := Finsupp.mem_span_range_iff_exists_finsupp.mp hv
  have hc' (g : G) : ∑ b ∈ c.support, c b * (g • b) = v g := by
    simpa only [Finsupp.sum, Finset.sum_apply, Pi.smul_apply, smul_eq_mul, orbitProfile]
      using congrFun hc g
  refine ⟨c.support, c, fun x ↦ ?_⟩
  change ∑ b ∈ c.support, (∑ g : G, g • (b * x)) * c b = x
  simp only [MulSemiringAction.smul_mul, Finset.sum_mul]
  rw [Finset.sum_comm]
  have he (g : G) :
      ∑ b ∈ c.support, ((g • b) * (g • x)) * c b = v g * (g • x) := by
    rw [← hc' g, Finset.sum_mul]
    apply Finset.sum_congr rfl
    intro b _
    ring
  simp_rw [he]
  rw [Fintype.sum_eq_single 1 (fun g hg ↦ by rw [hv₀ g hg, zero_mul]),
    hv₁, one_smul, one_mul]

omit [Fintype G] in
/-- Freeness presents the original ring as a retract of an actual finite free module. -/
theorem exists_finite_free_retraction [Finite G] :
    ∃ (s : Finset A) (i : A →ₗ[invariantRing G A] (s → invariantRing G A))
      (r : (s → invariantRing G A) →ₗ[invariantRing G A] A),
      r.comp i = LinearMap.id := by
  classical
  let _ := Fintype.ofFinite G
  obtain ⟨s, a, ha⟩ := exists_trace_dual_generators G hfree
  let i : A →ₗ[invariantRing G A] (s → invariantRing G A) :=
    LinearMap.pi (fun b ↦ weightedTraceLinear G b.val)
  let r : (s → invariantRing G A) →ₗ[invariantRing G A] A :=
    ∑ b : s, (LinearMap.proj b).smulRight (a b.val)
  refine ⟨s, i, r, ?_⟩
  ext x
  simp only [r, i, LinearMap.comp_apply, LinearMap.sum_apply,
    LinearMap.smulRight_apply, LinearMap.proj_apply, LinearMap.pi_apply,
    LinearMap.id_apply]
  exact (Finset.sum_coe_sort s (fun b ↦ weightedTraceLinear G b x • a b)).trans (ha x)

omit [Fintype G] in
/-- The original source coordinates are projective over their invariant ring. -/
theorem invariant_module_projective [Finite G] : Module.Projective (invariantRing G A) A := by
  obtain ⟨s, i, r, hr⟩ := exists_finite_free_retraction G hfree
  exact Module.Projective.of_split i r hr

omit [Fintype G] in
/-- The original source coordinates are finite over their invariant ring. -/
theorem invariant_module_finite [Finite G] : Module.Finite (invariantRing G A) A := by
  obtain ⟨s, i, r, hr⟩ := exists_finite_free_retraction G hfree
  apply Module.Finite.of_surjective r
  intro x
  exact ⟨i x, DFunLike.congr_fun hr x⟩

end FLT.Mazur.FiniteGroupQuotient
