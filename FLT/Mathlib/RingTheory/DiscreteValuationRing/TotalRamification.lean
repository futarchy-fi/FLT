/-
Copyright (c) 2026 krandder. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: krandder
-/
module

public import FLT.Mathlib.RingTheory.DiscreteValuationRing.Monogenic
public import Mathlib.RingTheory.RamificationInertia.Basic
public import Mathlib.RingTheory.RamificationInertia.Ramification
public import Mathlib.LinearAlgebra.FreeModule.PID

/-!
# Totally ramified finite DVR algebras

When the base ring surjects onto the residue field, every uniformizer is an
integral power-basis generator. The module rank equals the additive valuation
of a base uniformizer.
-/

@[expose] public noncomputable section

open IsLocalRing

namespace IsDiscreteValuationRing

variable {R S : Type*} [CommRing R] [IsDomain R] [IsDiscreteValuationRing R]
  [CommRing S] [IsDomain S] [IsDiscreteValuationRing S] [Algebra R S]
  [Module.Finite R S] [FaithfulSMul R S]

omit [IsDomain R] [IsDiscreteValuationRing R] [FaithfulSMul R S] in
/-- Surjectivity onto the residue field makes every uniformizer an integral
generator of a finite DVR algebra. -/
theorem adjoinUniformizerEqTop (hres : ∀ s : S, ∃ r : R,
    residue S (algebraMap R S r) = residue S s) {y : S} (hy : Irreducible y) :
    Algebra.adjoin R {y} = ⊤ := by
  apply Subalgebra.eq_top_of_residue_surjective_of_irreducible _ ?_ hy
    (Algebra.subset_adjoin (Set.mem_singleton y))
  intro s
  obtain ⟨r, hr⟩ := hres s
  exact ⟨algebraMap R (Algebra.adjoin R {y}) r, hr⟩

/-- An integral power basis can be chosen with any specified uniformizer as generator. -/
theorem existsUniformizerPowerBasis (hres : ∀ s : S, ∃ r : R,
    residue S (algebraMap R S r) = residue S s) {y : S} (hy : Irreducible y) :
    ∃ pb : PowerBasis R S, pb.gen = y := by
  let h := IsAdjoinRootMonic.mkOfAdjoinEqTop' (adjoinUniformizerEqTop hres hy)
  exact ⟨h.powerBasis, by simp [h]⟩

/-- The additive valuation of an image of a base uniformizer is the
ramification index of the maximal ideal. -/
theorem addValMapUniformizerEqRamificationIdx {π : R} (hπ : Irreducible π) :
    addVal S (algebraMap R S π) = ((maximalIdeal S).ramificationIdx R : ℕ∞) := by
  obtain ⟨y, hy⟩ := exists_irreducible S
  have hπ0 : algebraMap R S π ≠ 0 :=
    map_ne_zero_iff _ (FaithfulSMul.algebraMap_injective R S) |>.mpr hπ.ne_zero
  obtain ⟨n, u, hu⟩ := eq_unit_mul_pow_irreducible hπ0 hy
  have hmap : (maximalIdeal R).map (algebraMap R S) = maximalIdeal S ^ n := by
    rw [hπ.maximalIdeal_eq, Ideal.map_span, Set.image_singleton, hu,
      Ideal.span_singleton_mul_left_unit u.isUnit, ← Ideal.span_singleton_pow,
      ← hy.maximalIdeal_eq]
  have hmap0 : (maximalIdeal R).map (algebraMap R S) ≠ ⊥ := by
    rw [hπ.maximalIdeal_eq, Ideal.map_span, Set.image_singleton,
      ne_eq, Ideal.span_singleton_eq_bot]
    exact hπ0
  have hirr : Irreducible (maximalIdeal S) :=
    ((Ideal.prime_iff_isPrime (not_a_field S)).mpr inferInstance).irreducible
  rw [hu, addVal_def' u hy n,
    Ideal.IsDedekindDomain.ramificationIdx_eq_normalizedFactors_count
      (maximalIdeal R) (maximalIdeal S) hmap0, hmap]
  simp [UniqueFactorizationMonoid.normalizedFactors_pow,
    UniqueFactorizationMonoid.normalizedFactors_irreducible hirr]

/-- A finite DVR algebra with unchanged residue field has module rank equal
to the valuation of a base uniformizer. -/
theorem finrankEqAddValMapUniformizer (hres : ∀ s : S, ∃ r : R,
    residue S (algebraMap R S r) = residue S s) {π : R} (hπ : Irreducible π) :
    (Module.finrank R S : ℕ∞) = addVal S (algebraMap R S π) := by
  classical
  let p := maximalIdeal R
  let q := maximalIdeal S
  let instIntegral : Algebra.IsIntegral R S := .of_finite R S
  let instUnique : Unique (p.primesOver S) :=
    ⟨⟨Ideal.primesOver.mk p q⟩, fun Q => Subtype.ext (eq_maximalIdeal inferInstance)⟩
  have hf : q.inertiaDeg R = 1 := by
    rw [Ideal.inertiaDeg_eq_of_isMaximal p q]
    apply Module.finrank_of_bijective_algebraMap
    refine ⟨(algebraMap (ResidueField R) (ResidueField S)).injective, ?_⟩
    intro z
    obtain ⟨s, rfl⟩ := residue_surjective (R := S) z
    obtain ⟨r, hr⟩ := hres s
    exact ⟨residue R r, by
      change residue S (algebraMap R S r) = residue S s
      exact hr⟩
  have he : q.ramificationIdx R = Module.finrank R S := by
    have h := Ideal.sum_ramification_inertia_eq_finrank (S := S) p
    rw [Fintype.sum_unique] at h
    change q.ramificationIdx R * q.inertiaDeg R = Module.finrank R S at h
    simpa only [hf, mul_one] using h
  rw [addValMapUniformizerEqRamificationIdx hπ, he]

end IsDiscreteValuationRing
