/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.FiniteErrorReductionFrame

/-!
# Constructing full reduction matrices from cokernel relations

A relation modulo the correction image produces an actual correcting vector.
Finite cokernel frames therefore suffice: their representatives need not span
an invariant finite submodule before the correcting vectors are constructed.
-/

@[expose] public noncomputable section
namespace FLT.Mazur.FiniteErrorReduction
variable {R M N κ : Type*} [CommRing R]
  [AddCommGroup M] [Module R M] [AddCommGroup N] [Module R N]
  (F : M →ₗ[R] N) (I : Ideal R) [Fintype κ] (e : κ → N)
set_option quotPrecheck false in
local notation "π" => (LinearMap.range F).mkQ

/-- An ideal-weighted finite span has coefficients in the ideal on the same frame. -/
theorem exists_ideal_coefficients {y : N}
    (hy : y ∈ I • Submodule.span R (Set.range e)) :
    ∃ c : κ → R, (∀ j, c j ∈ I) ∧ y = ∑ j, c j • e j := by
  obtain ⟨c, hc, he⟩ :=
    (Submodule.mem_ideal_smul_span_iff_exists_sum I e y).mp hy
  refine ⟨c, hc, ?_⟩
  exact he.symm.trans (Finsupp.sum_fintype _ _ (fun _ ↦ zero_smul _ _))

/-- Lift a finite cokernel relation to an actual vector and an ideal-valued matrix row. -/
theorem exists_reduction_row (j : κ)
    (hj : π (e j) ∈ I • Submodule.span R (Set.range (fun k ↦ π (e k)))) :
    ∃ (v : M) (c : κ → R), (∀ k, c k ∈ I) ∧ e j - F v = ∑ k, c k • e k := by
  obtain ⟨c, hc, he⟩ := exists_ideal_coefficients I (fun k ↦ π (e k)) hj
  have hz : e j - ∑ k, c k • e k ∈ LinearMap.range F := by
    apply (Submodule.Quotient.mk_eq_zero _).mp
    change π (e j - ∑ k, c k • e k) = 0
    rw [map_sub, map_sum]
    simp only [map_smul]
    exact sub_eq_zero.mpr he
  obtain ⟨v, hv⟩ := hz
  exact ⟨v, c, hc, by rw [hv, sub_sub_cancel]⟩

/-- Cokernel divisibility constructs all full correcting vectors and matrix entries. -/
theorem exists_reduction_matrix
    (h : Submodule.span R (Set.range (fun k ↦ π (e k))) ≤
      I • Submodule.span R (Set.range (fun k ↦ π (e k)))) :
    ∃ (v : κ → M) (c : κ → κ → R), (∀ j k, c j k ∈ I) ∧
      ∀ j, e j - F (v j) = ∑ k, c j k • e k := by
  have hr (j : κ) := exists_reduction_row F I e j (h (Submodule.subset_span ⟨j, rfl⟩))
  choose v c hc he using hr
  exact ⟨v, c, hc, he⟩

/-- Membership of the initial cokernel error constructs an initial full error expression. -/
theorem exists_initial_expression (y : N)
    (hy : π y ∈ Submodule.span R (Set.range (fun k ↦ π (e k)))) :
    ∃ (z : M) (b : κ → R), y - F z = ∑ k, b k • e k := by
  obtain ⟨b, hb⟩ := (Submodule.mem_span_range_iff_exists_fun R).mp hy
  have hz : y - ∑ k, b k • e k ∈ LinearMap.range F := by
    apply (Submodule.Quotient.mk_eq_zero _).mp
    change π (y - ∑ k, b k • e k) = 0
    rw [map_sub, map_sum]
    simp only [map_smul]
    exact sub_eq_zero.mpr hb.symm
  obtain ⟨z, hz⟩ := hz
  exact ⟨z, b, by rw [hz, sub_sub_cancel]⟩

end FLT.Mazur.FiniteErrorReduction
