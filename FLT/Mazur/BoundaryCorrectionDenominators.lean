/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.BoundaryCorrectionQuotient
public import Mathlib.RingTheory.Support

/-!
# Exact denominator ideals for individual boundary corrections

Each original numerator has its own correction ideal. The full boundary
support is their union of zero loci; it need not equal the zero locus of the
intersection. Finite scalar combinations explicitly patch actual corrections.
-/

@[expose] public noncomputable section
open scoped BigOperators
namespace FLT.Mazur.BoundaryCorrectionQuotient
variable {R M B : Type*} [CommRing R] [AddCommGroup M] [Module R M]
  [AddCommGroup B] [Module R B] (C : Submodule R M) (β : M →ₗ[R] B)

/-- The original scalar denominators that permit a correction of this numerator. -/
def denominatorIdeal (a : M) : Ideal R := (correctable C β).colon {a}

/-- Ideal membership constructs a correction in the actual boundary kernel. -/
theorem mem_denominatorIdeal (a : M) (x : R) :
    x ∈ denominatorIdeal C β a ↔ ∃ w : M, β w = 0 ∧ x • a - w ∈ C := by
  change x ∈ (correctable C β).colon {a} ↔ _
  rw [Submodule.mem_colon]
  simpa only [Set.mem_singleton_iff, forall_eq] using
    mem_correctable_iff C β (x • a)

/-- A numerator is correctable precisely when its denominator ideal is the unit ideal. -/
theorem denominatorIdeal_eq_top_iff (a : M) :
    denominatorIdeal C β a = ⊤ ↔ a ∈ correctable C β := by
  rw [Ideal.eq_top_iff_one, mem_denominatorIdeal, one_smul, mem_correctable_iff]

/-- A scalar combination of local corrections gives an explicit original correction. -/
theorem patch_corrections {ι : Type*} (s : Finset ι) (a : M) (x r : ι → R) (w : ι → M)
    (hw : ∀ i ∈ s, β (w i) = 0) (hc : ∀ i ∈ s, x i • a - w i ∈ C) :
    β (∑ i ∈ s, r i • w i) = 0 ∧
      (∑ i ∈ s, r i * x i) • a - ∑ i ∈ s, r i • w i ∈ C := by
  constructor
  · simp only [map_sum, map_smul]
    exact Finset.sum_eq_zero fun i hi ↦ by rw [hw i hi, smul_zero]
  · have h := C.sum_mem fun i hi ↦ C.smul_mem (r i) (hc i hi)
    simpa only [smul_sub, smul_smul, Finset.sum_sub_distrib, Finset.sum_smul] using h

/-- A partition of unity patches scalar corrections to a compatible lift with the same boundary. -/
theorem patch_lift {ι : Type*} (s : Finset ι) (a : M) (x r : ι → R) (w : ι → M)
    (hw : ∀ i ∈ s, β (w i) = 0) (hc : ∀ i ∈ s, x i • a - w i ∈ C)
    (hunit : ∑ i ∈ s, r i * x i = 1) :
    a - ∑ i ∈ s, r i • w i ∈ C ∧ β (a - ∑ i ∈ s, r i • w i) = β a := by
  obtain ⟨hb, hm⟩ := patch_corrections C β s a x r w hw hc
  rw [hunit, one_smul] at hm
  exact ⟨hm, by rw [map_sub, hb, sub_zero]⟩

/-- Local power corrections on a scalar principal cover construct a global correction. -/
theorem correctable_of_scalar_cover (a : M) (S : Set R) (hS : Ideal.span S = ⊤)
    (h : ∀ x ∈ S, ∃ k : ℕ, ∃ w : M, β w = 0 ∧ x ^ k • a - w ∈ C) :
    a ∈ correctable C β := by
  apply (denominatorIdeal_eq_top_iff C β a).mp
  apply Ideal.radical_eq_top.mp
  apply top_unique
  rw [← hS, Ideal.span_le]
  intro x hx
  obtain ⟨k, w, hw, hc⟩ := h x hx
  exact ⟨k, (mem_denominatorIdeal C β a (x ^ k)).mpr ⟨w, hw, hc⟩⟩

/-- Local vanishing uses one exact denominator per original numerator. -/
theorem not_support_iff_denominators (hβ : Function.Surjective β) (P : PrimeSpectrum R) :
    P ∉ Module.support R (B ⧸ C.map β) ↔
      ∀ a : M, ∃ x : R, x ∉ P.asIdeal ∧ x ∈ denominatorIdeal C β a := by
  rw [Module.notMem_support_iff']
  constructor
  · intro h a
    obtain ⟨x, hx, hz⟩ := h ((C.map β).mkQ (β a))
    refine ⟨x, hx, ?_⟩
    apply (mem_denominatorIdeal C β a x).mpr
    apply (mem_correctable_iff C β (x • a)).mp
    change β (x • a) ∈ C.map β
    rw [map_smul]
    apply (Submodule.Quotient.mk_eq_zero (C.map β)).mp
    exact hz
  · intro h q
    obtain ⟨a, rfl⟩ := obstruction_surjective C β hβ q
    obtain ⟨x, hx, hw⟩ := h a
    refine ⟨x, hx, ?_⟩
    have ha := (mem_correctable_iff C β (x • a)).mpr
      ((mem_denominatorIdeal C β a x).mp hw)
    change β (x • a) ∈ C.map β at ha
    change (C.map β).mkQ (x • β a) = 0
    rw [← map_smul]
    exact (Submodule.Quotient.mk_eq_zero (C.map β)).mpr ha

/-- A supported prime is witnessed by one original numerator's whole correction ideal. -/
theorem mem_support_iff_denominator_le (hβ : Function.Surjective β) (P : PrimeSpectrum R) :
    P ∈ Module.support R (B ⧸ C.map β) ↔
      ∃ a : M, denominatorIdeal C β a ≤ P.asIdeal := by
  have he := not_congr (not_support_iff_denominators C β hβ P)
  push Not at he
  refine he.trans (exists_congr fun a ↦ ?_)
  constructor
  · intro h x hx
    by_contra hn
    exact h x hn hx
  · intro h x hx hJ
    exact hx (h hJ)

/-- No finiteness hypothesis is required for the union description of the exact boundary support. -/
theorem support_eq_iUnion (hβ : Function.Surjective β) :
    Module.support R (B ⧸ C.map β) =
      ⋃ a : M, PrimeSpectrum.zeroLocus (denominatorIdeal C β a : Set R) := by
  ext P
  rw [mem_support_iff_denominator_le C β hβ, Set.mem_iUnion]
  rfl

end FLT.Mazur.BoundaryCorrectionQuotient
