/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.SeparableAffineCoordinates
public import Mathlib.RingTheory.Spectrum.Prime.Topology

/-!
# Separable-coordinate points meet every geometric affine open

The geometric open may be defined by polynomials with transcendental
coefficients. Its nonemptiness still supplies a point all of whose affine
coordinates are separable over the original field.
-/

@[expose] public noncomputable section
namespace FLT.Mazur.SeparableAffineOpenPoints
variable {k K : Type} [Field k] [Field K] [Algebra k K] {σ : Type}

/-- The actual prime-spectrum point defined by evaluating the coordinate tuple. -/
def point (v : σ → K) : PrimeSpectrum (MvPolynomial σ K) :=
  PrimeSpectrum.comap (MvPolynomial.eval v) ⟨⊥, inferInstance⟩

/-- Membership in a principal open is precisely nonvanishing at the tuple. -/
theorem point_mem_basicOpen (v : σ → K) (p : MvPolynomial σ K) :
    point v ∈ PrimeSpectrum.basicOpen p ↔ MvPolynomial.eval v p ≠ 0 := by
  change ¬ MvPolynomial.eval v p ∈ (⊥ : Ideal K) ↔ _
  rw [Ideal.mem_bot]

/-- Every nonempty geometric affine open contains a separable-coordinate evaluation point. -/
theorem exists_point [IsSepClosed K] (U : Set (PrimeSpectrum (MvPolynomial σ K)))
    (hU : IsOpen U) (hne : U.Nonempty) :
    ∃ v : σ → K, (∀ i, IsSeparable k (v i)) ∧ point v ∈ U := by
  obtain ⟨x, hx⟩ := hne
  obtain ⟨_, ⟨p, rfl⟩, hxp, hpU⟩ :=
    PrimeSpectrum.isTopologicalBasis_basic_opens.exists_subset_of_mem_open hx hU
  have hp : p ≠ 0 := by
    intro h
    exact (PrimeSpectrum.mem_basicOpen p x).mp hxp (h ▸ x.asIdeal.zero_mem)
  obtain ⟨v, hv, hpv⟩ :=
    SeparableAffineCoordinates.exists_separable_eval_ne_zero (k := k) p hp
  exact ⟨v, hv, hpU ((point_mem_basicOpen v p).mpr hpv)⟩

/-- The separable-coordinate grid is dense in the whole geometric affine space. -/
theorem dense_points [IsSepClosed K] :
    Dense {x : PrimeSpectrum (MvPolynomial σ K) |
      ∃ v : σ → K, (∀ i, IsSeparable k (v i)) ∧ point v = x} := by
  rw [dense_iff_inter_open]
  intro U hU hne
  obtain ⟨v, hv, hp⟩ := exists_point (k := k) U hU hne
  exact ⟨point v, hp, v, hv, rfl⟩

end FLT.Mazur.SeparableAffineOpenPoints
