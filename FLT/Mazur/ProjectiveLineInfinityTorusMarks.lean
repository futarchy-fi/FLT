/-
Copyright (c) 2026 krandder. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: krandder
-/
module

public import FLT.Mazur.ProjectiveLineInfinityTorusGluing
public import Mathlib.RingTheory.Polynomial.Quotient

/-!
# The ordered complement of the infinity torus

The entire translated torus is the projective line minus the two original
slope markings 0 and -a. This accounts for all scheme points, over any field.
-/

@[expose] public noncomputable section
open AlgebraicGeometry CategoryTheory Polynomial
open scoped LaurentPolynomial
namespace FLT.Mazur.ProjectiveLine
open WeierstrassModificationX
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
universe u
variable {K : Type u} [Field K] (a : Kˣ)

/-- A marking in the original slope affine coordinate. -/
def infinitySlopeMark (c : K) : Spec (.of K) ⟶ scheme K :=
  Spec.map (CommRingCat.ofHom (aeval c).toRingHom) ≫ left K

/-- The left-chart inverse image of the full torus retains both original factors. -/
theorem left_preimage_infinityTorus : (left K) ⁻¹' Set.range (infinityTorusChart a) =
    (PrimeSpectrum.basicOpen (slopePolynomial (a : K)) : Set (PrimeSpectrum K[X])) := by
  have h := IsOpenImmersion.image_preimage_eq_preimage_image_of_isPullback
    (infinityTorus_isPullback a).flip ⊤
  have he : (left K) ⁻¹' Set.range (infinityTorusChart a) =
      Set.range (PrincipalOpenTransport.inclusion (slopePolynomial (a : K))) := by
    simpa using (congrArg SetLike.coe h).symm
  rw [he]
  exact PrimeSpectrum.localization_away_comap_range _ _

/-- Evaluation at c has exactly the full zero locus of X-c. -/
theorem infinitySlope_eval_range (c : K) :
    Set.range (Spec.map (CommRingCat.ofHom (aeval c).toRingHom)) =
      PrimeSpectrum.zeroLocus ({X - C c} : Set K[X]) := by
  change Set.range (PrimeSpectrum.comap (evalRingHom c)) = _
  rw [range_comap_of_surjective K _ (fun r => ⟨C r, by simp⟩),
    ker_evalRingHom, PrimeSpectrum.zeroLocus_span]

/-- The original two marked fibers are disjoint from the entire infinity torus. -/
theorem infinitySlopeMark_not_torus (c : K) (hc : c = 0 ∨ c = -(a : K))
    (x : Spec (.of K)) : infinitySlopeMark c x ∉ Set.range (infinityTorusChart a) := by
  change Spec.map (CommRingCat.ofHom (aeval c).toRingHom) x ∉
    (left K) ⁻¹' Set.range (infinityTorusChart a)
  rw [left_preimage_infinityTorus]
  change ¬ (aeval c (slopePolynomial (a : K)) ∉ x.asIdeal)
  have hz : aeval c (slopePolynomial (a : K)) = 0 := by
    rcases hc with rfl | rfl <;> simp [slopePolynomial]
  rw [hz]
  exact not_not_intro x.asIdeal.zero_mem

/-- Every point belongs to the full torus or one of the two ordered original node markings. -/
theorem infinityTorus_or_marks (x : scheme K) :
    x ∈ Set.range (infinityTorusChart a) ∨
      x ∈ Set.range (infinitySlopeMark (0 : K)) ∨
        x ∈ Set.range (infinitySlopeMark (-(a : K))) := by
  rcases infinityTorus_charts_cover a x with ⟨y, rfl⟩ | ht
  · by_cases hy : y ∈ PrimeSpectrum.basicOpen (slopePolynomial (a : K))
    · left
      change y ∈ (left K) ⁻¹' Set.range (infinityTorusChart a)
      rw [left_preimage_infinityTorus]
      exact hy
    · have hm : slopePolynomial (a : K) ∈ y.asIdeal := not_not.mp hy
      rcases y.isPrime.mem_or_mem hm with h0 | ha
      · right; left
        have hr : y ∈ Set.range (Spec.map (CommRingCat.ofHom (aeval (0 : K)).toRingHom)) := by
          rw [infinitySlope_eval_range]
          change ({X - C (0 : K)} : Set K[X]) ⊆ y.asIdeal
          simp only [C_0, sub_zero, Set.singleton_subset_iff]
          exact h0
        obtain ⟨z, rfl⟩ := hr
        exact ⟨z, rfl⟩
      · right; right
        have hr : y ∈ Set.range (Spec.map (CommRingCat.ofHom (aeval (-(a : K))).toRingHom)) := by
          rw [infinitySlope_eval_range]
          change ({X - C (-(a : K))} : Set K[X]) ⊆ y.asIdeal
          simp only [map_neg, sub_neg_eq_add, Set.singleton_subset_iff]
          exact ha
        obtain ⟨z, rfl⟩ := hr
        exact ⟨z, rfl⟩
  · exact Or.inl ht

/-- The full torus is exactly the complement of the two original marked fibers. -/
theorem infinityTorus_range_complement : Set.range (infinityTorusChart a) =
    (Set.range (infinitySlopeMark (0 : K)) ∪
      Set.range (infinitySlopeMark (-(a : K))))ᶜ := by
  ext x
  constructor
  · intro hx hmarks
    rcases hmarks with ⟨z, rfl⟩ | ⟨z, rfl⟩
    · exact infinitySlopeMark_not_torus a 0 (Or.inl rfl) z hx
    · exact infinitySlopeMark_not_torus a (-(a : K)) (Or.inr rfl) z hx
  · intro hx
    rcases infinityTorus_or_marks a x with ht | h0 | ha
    · exact ht
    · exact False.elim (hx (Or.inl h0))
    · exact False.elim (hx (Or.inr ha))

end FLT.Mazur.ProjectiveLine
