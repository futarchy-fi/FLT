/-
Copyright (c) 2026 krandder. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: krandder
-/
module

public import FLT.Mathlib.RingTheory.DiscreteValuationRing.PolynomialValuation
public import FLT.Mathlib.RingTheory.DifferentPowerBasis
public import Mathlib.Algebra.Polynomial.Derivative

/-!
# A degree bound for the different in a totally ramified DVR extension

Distinct term valuations in a uniformizer expansion bound the derivative
by its leading term. In a uniformizer power basis this proves that the
different contains `e * y^(e-1)`, where `e` is the extension degree.
-/

@[expose] public noncomputable section

open Polynomial IsLocalRing IsDiscreteValuationRing

namespace Polynomial.Monic

variable {R S : Type*} [CommRing R] [IsDomain R] [IsDiscreteValuationRing R]
  [CharZero R] [CommRing S] [IsDomain S] [IsDiscreteValuationRing S] [Algebra R S]

/-- The valuation of the derivative at a uniformizer is bounded by its leading term. -/
theorem addVal_derivative_aeval_le {P : R[X]} (hP : P.Monic)
    (hn : 0 < P.natDegree) {π : R} (hπ : Irreducible π)
    (he : addVal S (algebraMap R S π) = (P.natDegree : ℕ∞))
    {y : S} (hy : Irreducible y) :
    addVal S (aeval y P.derivative) ≤
      addVal S (P.natDegree : S) + (P.natDegree - 1 : ℕ) := by
  have hc : P.derivative.coeff (P.natDegree - 1) = (P.natDegree : R) := by
    rw [coeff_derivative, Nat.sub_add_cancel hn, hP.coeff_natDegree, one_mul]
    norm_cast
    exact Nat.sub_add_cancel hn
  have h := addVal_aeval_le_term hπ he hy P.derivative (natDegree_derivative_lt hn.ne')
    (Nat.sub_lt hn (by decide : 0 < 1)) (by rw [hc]; exact Nat.cast_ne_zero.mpr hn.ne')
  simpa only [hc, map_natCast, addVal_mul, hy.addVal_pow] using h

end Polynomial.Monic

namespace PowerBasis

variable {R S : Type*} [CommRing R] [IsDomain R] [IsDiscreteValuationRing R]
  [CharZero R] [CommRing S] [IsDomain S] [IsDiscreteValuationRing S] [Algebra R S]
  [Module.Finite R S] [FaithfulSMul R S]

/-- A uniformizer power basis in a totally ramified extension has the classical
upper bound `v(e) + e - 1` for the valuation of its different generator. -/
theorem addVal_minpoly_derivative_le (pb : PowerBasis R S) (hy : Irreducible pb.gen)
    (hres : ∀ s : S, ∃ r : R, residue S (algebraMap R S r) = residue S s) :
    addVal S (aeval pb.gen (minpoly R pb.gen).derivative) ≤
      addVal S (pb.dim : S) + (pb.dim - 1 : ℕ) := by
  obtain ⟨π, hπ⟩ := exists_irreducible R
  have he : addVal S (algebraMap R S π) = ((minpoly R pb.gen).natDegree : ℕ∞) := by
    rw [← finrankEqAddValMapUniformizer hres hπ, pb.finrank, pb.natDegree_minpoly]
  simpa only [pb.natDegree_minpoly] using
    (minpoly.monic pb.isIntegral_gen).addVal_derivative_aeval_le
      (minpoly.natDegree_pos pb.isIntegral_gen) hπ he hy

/-- The degree times the `(degree-1)`st uniformizer power lies in the different. -/
theorem degree_mul_uniformizer_pow_mem_different
    (K L : Type*) [Field K] [Field L] [Algebra R K] [IsFractionRing R K]
    [Algebra S L] [IsFractionRing S L] [Algebra R L] [Algebra K L]
    [IsScalarTower R K L] [IsScalarTower R S L] [FiniteDimensional K L]
    [Algebra.IsSeparable K L] (pb : PowerBasis R S) (hy : Irreducible pb.gen)
    (hres : ∀ s : S, ∃ r : R, residue S (algebraMap R S r) = residue S s) :
    (pb.dim : S) * pb.gen ^ (pb.dim - 1) ∈ differentIdeal R S := by
  rw [pb.differentIdeal_eq_span_minpoly_derivative K L, Ideal.mem_span_singleton,
    ← addVal_le_iff_dvd, addVal_mul, hy.addVal_pow]
  exact pb.addVal_minpoly_derivative_le hy hres

/-- Multiplying a base uniformizer by the extension degree gives an element
of the different, without retaining the top uniformizer in the bound. -/
theorem degree_mul_baseUniformizer_mem_different
    (K L : Type*) [Field K] [Field L] [Algebra R K] [IsFractionRing R K]
    [Algebra S L] [IsFractionRing S L] [Algebra R L] [Algebra K L]
    [IsScalarTower R K L] [IsScalarTower R S L] [FiniteDimensional K L]
    [Algebra.IsSeparable K L] (pb : PowerBasis R S) (hy : Irreducible pb.gen)
    (hres : ∀ s : S, ∃ r : R, residue S (algebraMap R S r) = residue S s)
    {π : R} (hπ : Irreducible π) :
    algebraMap R S ((pb.dim : R) * π) ∈ differentIdeal R S := by
  rw [pb.differentIdeal_eq_span_minpoly_derivative K L, Ideal.mem_span_singleton,
    ← addVal_le_iff_dvd, map_mul, map_natCast, addVal_mul,
    ← finrankEqAddValMapUniformizer hres hπ, pb.finrank]
  exact (pb.addVal_minpoly_derivative_le hy hres).trans
    (add_le_add le_rfl (by exact_mod_cast Nat.sub_le pb.dim 1))

end PowerBasis

namespace IsDiscreteValuationRing

variable {R S : Type*} [CommRing R] [IsDomain R] [IsDiscreteValuationRing R]
  [CharZero R] [CommRing S] [IsDomain S] [IsDiscreteValuationRing S] [Algebra R S]
  [Module.Finite R S] [FaithfulSMul R S]

/-- A finite totally ramified DVR extension has different containing the
base uniformizer times its rank; no chosen power basis is an input. -/
theorem finrank_mul_uniformizer_mem_different
    (K L : Type*) [Field K] [Field L] [Algebra R K] [IsFractionRing R K]
    [Algebra S L] [IsFractionRing S L] [Algebra R L] [Algebra K L]
    [IsScalarTower R K L] [IsScalarTower R S L] [FiniteDimensional K L]
    [Algebra.IsSeparable K L]
    (hres : ∀ s : S, ∃ r : R, residue S (algebraMap R S r) = residue S s)
    {π : R} (hπ : Irreducible π) :
    algebraMap R S ((Module.finrank R S : R) * π) ∈ differentIdeal R S := by
  obtain ⟨y, hy⟩ := exists_irreducible S
  obtain ⟨pb, hpb⟩ := existsUniformizerPowerBasis hres hy
  rw [pb.finrank]
  exact pb.degree_mul_baseUniformizer_mem_different K L (hpb.symm ▸ hy) hres hπ

end IsDiscreteValuationRing
