/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.FiniteGroupFreeTraceIdeal

/-!
# Invariant boundary lifts for free finite actions

The unit trace ideal constructs an element with orbit trace one. Its weighted
orbit sums lift every invariant function along an equivariant surjection.
Thus the actual boundary certificates are proved for these tests, in arbitrary
characteristic and without invariant finite-generation assumptions.
-/

@[expose] public noncomputable section
open scoped BigOperators
namespace FLT.Mazur.FiniteGroupQuotient
variable (G : Type*) [Group G] [Fintype G]
variable {A : Type*} [CommRing A] [MulSemiringAction G A]

/-- Orbit traces are additive. -/
theorem orbitTrace_add (a b : A) : orbitTrace G (a + b) = orbitTrace G a + orbitTrace G b := by
  apply Subtype.ext
  change (∑ g : G, g • (a + b)) = (∑ g : G, g • a) + ∑ g : G, g • b
  simp only [smul_add, Finset.sum_add_distrib]

/-- Invariant coefficients can be brought inside the trace. -/
theorem orbitTrace_mul_invariant (a : invariantRing G A) (b : A) :
    orbitTrace G (a.val * b) = a * orbitTrace G b := by
  apply Subtype.ext
  have ha : ∀ g : G, g • a.val = a.val := a.property
  change (∑ g : G, g • (a.val * b)) = a.val * ∑ g : G, g • b
  simp only [MulSemiringAction.smul_mul, ha, Finset.mul_sum]

/-- Actual traces form an ideal of the invariant ring. -/
def orbitTraceRange : Ideal (invariantRing G A) where
  carrier := Set.range (orbitTrace G)
  zero_mem' := ⟨0, Subtype.ext (by simp [orbitTrace])⟩
  add_mem' := by
    rintro _ _ ⟨a, rfl⟩ ⟨b, rfl⟩
    exact ⟨a + b, orbitTrace_add G a b⟩
  smul_mem' := by
    rintro a _ ⟨b, rfl⟩
    exact ⟨a.val * b, orbitTrace_mul_invariant G a b⟩

/-- Freeness constructs a trace-one weight in the original source ring. -/
theorem exists_orbitTrace_one
    (hfree : ∀ g : G, g ≠ 1 → fixedPointIdeal G A g = ⊤) :
    ∃ a : A, orbitTrace G a = 1 := by
  have hle : invariantTraceIdeal G A ≤ orbitTraceRange G := Ideal.span_le.mpr (fun _ h ↦ h)
  rw [invariantTraceIdeal_eq_top G A hfree] at hle
  exact hle (show (1 : invariantRing G A) ∈ (⊤ : Ideal _) from trivial)

variable {B : Type*} [CommRing B] [MulSemiringAction G B]
  (f : A →+* B) (hf : ∀ (g : G) a, f (g • a) = g • f a)
  (hs : Function.Surjective f)
  (hfree : ∀ g : G, g ≠ 1 → fixedPointIdeal G A g = ⊤)

include hs hfree

omit [Fintype G] in
/-- Every invariant boundary function has an actual original invariant lift. -/
theorem boundaryMap_surjective_of_free [Finite G] : Function.Surjective (boundaryMap G f hf) := by
  let _ := Fintype.ofFinite G
  obtain ⟨a, ha⟩ := exists_orbitTrace_one G hfree
  intro t
  obtain ⟨b, hb⟩ := hs t.val
  refine ⟨orbitTrace G (a * b), ?_⟩
  rw [boundaryMap_weightedTrace G f hf t b hb a, ha, map_one, one_mul]

omit [Fintype G] in
/-- Every invariant section is certified on the full boundary source. -/
theorem boundary_certified_of_free [Finite G] (t : invariantRing G B) :
    t ∈ sourceCertifiedSections (boundaryMap G f hf) (inclusion G B) := by
  obtain ⟨a, rfl⟩ := boundaryMap_surjective_of_free G f hf hs hfree t
  exact image_mem_sourceCertifiedSections _ _ a

omit [Fintype G] in
/-- Freeness proves the finite coefficient identity for every invariant boundary section. -/
theorem boundary_certificate_of_free [Finite G] (t : invariantRing G B) :
    ∃ a : sectionLiftIdeal (boundaryMap G f hf) t →₀ B,
      a.sum (fun v b ↦ b * (boundaryMap G f hf v.val).val) = 1 :=
  (mem_sourceCertifiedSections_iff _ _ t).mp
    (boundary_certified_of_free G f hf hs hfree t)

end FLT.Mazur.FiniteGroupQuotient
