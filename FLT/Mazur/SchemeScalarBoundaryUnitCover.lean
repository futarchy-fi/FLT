/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.SchemeScalarBadPrimeDenominators
public import Mathlib.RingTheory.Ideal.Maximal
public import Mathlib.LinearAlgebra.Finsupp.LinearCombination

/-!
# Covering every original boundary prime by actual denominators

Universal avoidance is equivalent to the image of the exact denominator ideal
being the unit ideal in the boundary ring. A finite unit equation gives an
explicit sufficient certificate and selects a denominator at every prime.
-/

@[expose] public noncomputable section
open AlgebraicGeometry
namespace FLT.Mazur.SchemeScalarPrincipalNeighborhood
open SchemeOpenEnvelope
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
variable {R T : Type} [CommRing R] [CommRing T] {X : Scheme}
  (s : R →+* Γ(X, ⊤)) (O : X.Opens) (κ : R →+* T)

/-- Universal original boundary avoidance is exactly a unit image of the denominator ideal. -/
theorem scalar_boundary_cover_iff_unit_ideal :
    (∀ P : PrimeSpectrum T, PrimeSpectrum.comap κ P ∈ scalarNeighborhoodLocus s O) ↔
      Ideal.map κ (denominatorIdeal s O) = ⊤ := by
  constructor
  · intro h
    by_contra hn
    obtain ⟨M, hM, hle⟩ := Ideal.exists_le_maximal _ hn
    let _ := hM
    obtain ⟨r, hr, hO⟩ := (mem_scalarNeighborhoodLocus_iff s O _).mp (h ⟨M, inferInstance⟩)
    exact hr (hle (Ideal.mem_map_of_mem κ hO))
  · intro h P
    apply (mem_scalarNeighborhoodLocus_iff s O _).mpr
    have hn : ¬ denominatorIdeal s O ≤ P.asIdeal.comap κ := by
      intro hle
      have hmap := Ideal.map_le_iff_le_comap.mpr hle
      rw [h] at hmap
      exact P.isPrime.ne_top (top_le_iff.mp hmap)
    obtain ⟨r, hr, hP⟩ := IsConcreteLE.not_le_iff_exists.mp hn
    exact ⟨r, hP, hr⟩

/-- A finite boundary unit equation selects a full source denominator at each original prime. -/
theorem scalar_boundary_denominator_of_unit_sum {I : Type} [Fintype I]
    (a : I → R) (b : I → T) (ha : ∀ i, X.basicOpen (s (a i)) ≤ O)
    (hab : ∑ i, b i * κ (a i) = 1) (P : PrimeSpectrum T) :
    ∃ i, κ (a i) ∉ P.asIdeal ∧ X.basicOpen (s (a i)) ≤ O := by
  classical
  have hn : ∃ i, κ (a i) ∉ P.asIdeal := by
    by_contra h
    push Not at h
    have hm : (∑ i, b i * κ (a i)) ∈ P.asIdeal :=
      sum_mem (fun i _ ↦ P.asIdeal.mul_mem_left (b i) (h i))
    rw [hab] at hm
    exact P.isPrime.ne_top (Ideal.eq_top_of_isUnit_mem _ hm isUnit_one)
  obtain ⟨i, hi⟩ := hn
  exact ⟨i, hi, ha i⟩

/-- The same finite equation proves avoidance at every original boundary prime simultaneously. -/
theorem scalar_boundary_cover_of_unit_sum {I : Type} [Fintype I]
    (a : I → R) (b : I → T) (ha : ∀ i, X.basicOpen (s (a i)) ≤ O)
    (hab : ∑ i, b i * κ (a i) = 1) :
    ∀ P : PrimeSpectrum T, PrimeSpectrum.comap κ P ∈ scalarNeighborhoodLocus s O := by
  intro P
  obtain ⟨i, hi, hO⟩ := scalar_boundary_denominator_of_unit_sum s O κ a b ha hab P
  exact (mem_scalarNeighborhoodLocus_iff s O _).mpr ⟨a i, hi, hO⟩

/-- Extract a finite unit equation from the unit image ideal, without Noetherian hypotheses. -/
theorem scalar_boundary_unit_ideal_iff_finite_equation :
    Ideal.map κ (denominatorIdeal s O) = ⊤ ↔
      ∃ (n : ℕ) (a : Fin n → R) (b : Fin n → T),
        (∀ i, X.basicOpen (s (a i)) ≤ O) ∧ ∑ i, b i * κ (a i) = 1 := by
  classical
  constructor
  · intro h
    have hone : (1 : T) ∈ Submodule.span T (κ '' (denominatorIdeal s O : Set R)) := by
      change (1 : T) ∈ Ideal.map κ (denominatorIdeal s O)
      rw [h]
      trivial
    obtain ⟨n, b, g, hg⟩ := Submodule.mem_span_set'.mp hone
    choose a ha hκ using fun i ↦ (g i).property
    refine ⟨n, a, b, ha, ?_⟩
    calc
      ∑ i, b i * κ (a i) = ∑ i, b i * (g i).val := by
        apply Finset.sum_congr rfl
        intro i _
        rw [hκ i]
      _ = 1 := hg
  · rintro ⟨n, a, b, ha, hab⟩
    rw [Ideal.eq_top_iff_one, ← hab]
    exact sum_mem fun i _ ↦
      (Ideal.map κ (denominatorIdeal s O)).mul_mem_left (b i) (Ideal.mem_map_of_mem κ (ha i))

end FLT.Mazur.SchemeScalarPrincipalNeighborhood
