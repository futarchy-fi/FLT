/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.FiniteRelationDetection
public import Mathlib.RingTheory.Spectrum.Prime.Topology

/-!
# Principal covers descend through finite-relation approximations

A finite family covering the limiting affine quotient covers at a later
stage. Lift the coefficients of a unit-ideal equation, then impose its single
remaining equality. No injectivity of the quotient maps is required.
-/

@[expose] public noncomputable section

namespace FLT.Mazur.FiniteRelationModel

universe u v w

variable {R : Type u} [CommRing R] {P : Type v} [CommRing P] [Algebra R P]
  (I : Ideal P)

/-- A finite principal cover of the quotient holds at a later relation stage. -/
theorem exists_principal_cover_stage {ι : Type w} [Fintype ι] (s : Finset I)
    (x : ι → Stage I s)
    (hx : (⨆ i, PrimeSpectrum.basicOpen (toQuotient R I s (x i))) = ⊤) :
    ∃ (t : Finset I) (hst : s ≤ t), ∃ c : ι → Stage I t,
      (∑ i, c i * transition R I hst (x i) = 1) ∧
      (⨆ i, PrimeSpectrum.basicOpen (transition R I hst (x i))) = ⊤ := by
  classical
  have hspan := PrimeSpectrum.iSup_basicOpen_eq_top_iff.mp hx
  obtain ⟨c, hc⟩ := Ideal.mem_span_range_iff_exists_fun.mp
    (show (1 : P ⧸ I) ∈ Ideal.span (Set.range fun i ↦ toQuotient R I s (x i)) by
      rw [hspan]
      trivial)
  choose a ha using fun i ↦ toQuotient_surjective R I s (c i)
  have he : toQuotient R I s (∑ i, a i * x i) = toQuotient R I s 1 := by
    simpa only [map_sum, map_mul, ha, map_one] using hc
  obtain ⟨t, hst, ht⟩ := exists_transition_eq R I s (∑ i, a i * x i) 1 he
  have hc' : ∑ i, transition R I hst (a i) * transition R I hst (x i) = 1 := by
    simpa only [map_sum, map_mul, map_one] using ht
  refine ⟨t, hst, fun i ↦ transition R I hst (a i), hc', ?_⟩
  apply PrimeSpectrum.iSup_basicOpen_eq_top_iff.mpr
  apply Ideal.eq_top_of_isUnit_mem _ ?_ isUnit_one
  exact Ideal.mem_span_range_iff_exists_fun.mpr ⟨_, hc'⟩

/-- An element invertible in the limiting quotient becomes invertible at a finite stage. -/
theorem exists_isUnit_stage (s : Finset I) (x : Stage I s)
    (hx : IsUnit (toQuotient R I s x)) :
    ∃ (t : Finset I) (hst : s ≤ t), IsUnit (transition R I hst x) := by
  obtain ⟨y, hy⟩ := isUnit_iff_exists_inv.mp hx
  obtain ⟨a, ha⟩ := toQuotient_surjective R I s y
  have he : toQuotient R I s (x * a) = toQuotient R I s 1 := by
    rw [map_mul, ha, hy, map_one]
  obtain ⟨t, hst, ht⟩ := exists_transition_eq R I s (x * a) 1 he
  refine ⟨t, hst, isUnit_iff_exists_inv.mpr ⟨transition R I hst a, ?_⟩⟩
  simpa only [map_mul, map_one] using ht

end FLT.Mazur.FiniteRelationModel
