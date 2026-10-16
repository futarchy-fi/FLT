/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.FiniteGroupFreeBoundaryLift

/-!
# Field-valued freeness supplies the boundary lifting construction

If a nonidentity group element had a proper fixed-point ideal, a maximal
ideal above it would give a fixed field-valued point. Thus freeness on actual
field-valued tests proves the unit fixed-point ideals used by the orbit-sum
construction; these identities need not be supplied separately.
-/

@[expose] public noncomputable section
namespace FLT.Mazur.FiniteGroupQuotient
universe u v
variable (G : Type v) [Group G] {A : Type u} [CommRing A] [MulSemiringAction G A]

/-- A field test exists whenever the scheme-theoretic fixed locus is nonempty. -/
theorem exists_fixed_field_test (g : G) (hg : fixedPointIdeal G A g ≠ ⊤) :
    ∃ (K : Type u) (_ : Field K) (φ : A →+* K), ∀ a : A, φ (g • a) = φ a := by
  obtain ⟨m, hm, hIm⟩ := Ideal.exists_le_maximal (fixedPointIdeal G A g) hg
  let _ := hm
  refine ⟨A ⧸ m, Ideal.Quotient.field m, Ideal.Quotient.mk m, ?_⟩
  intro a
  apply Eq.symm
  apply Ideal.Quotient.eq.mpr
  exact hIm (Ideal.subset_span ⟨a, rfl⟩)

/-- Freeness on field-valued points proves every nonidentity fixed-point ideal is one. -/
theorem fixedPointIdeal_eq_top_of_field_tests
    (hfree : ∀ (K : Type u) [Field K] (φ : A →+* K) (g : G),
      (∀ a : A, φ (g • a) = φ a) → g = 1) (g : G) (hg : g ≠ 1) :
    fixedPointIdeal G A g = ⊤ := by
  by_contra h
  obtain ⟨K, hK, φ, hφ⟩ := exists_fixed_field_test G g h
  exact hg (hfree K φ g hφ)

variable [Finite G] {B : Type u} [CommRing B] [MulSemiringAction G B]
  (f : A →+* B) (hf : ∀ (g : G) a, f (g • a) = g • f a)
  (hs : Function.Surjective f)
  (hfree : ∀ (K : Type u) [Field K] (φ : A →+* K) (g : G),
    (∀ a : A, φ (g • a) = φ a) → g = 1)
include hs hfree

/-- Geometric field-valued freeness produces every original invariant boundary lift. -/
theorem boundaryMap_surjective_of_field_tests : Function.Surjective (boundaryMap G f hf) :=
  boundaryMap_surjective_of_free G f hf hs (fixedPointIdeal_eq_top_of_field_tests G hfree)

/-- Every boundary section has a finite certificate, derived from field-valued freeness. -/
theorem boundary_certificate_of_field_tests (t : invariantRing G B) :
    ∃ a : sectionLiftIdeal (boundaryMap G f hf) t →₀ B,
      a.sum (fun v b ↦ b * (boundaryMap G f hf v.val).val) = 1 :=
  boundary_certificate_of_free G f hf hs (fixedPointIdeal_eq_top_of_field_tests G hfree) t

end FLT.Mazur.FiniteGroupQuotient
