/-
Copyright (c) 2026 krandder. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: krandder
-/
module

public import FLT.Mathlib.RingTheory.DiscreteValuationRing.Eisenstein
public import FLT.Mathlib.RingTheory.DiscreteValuationRing.TotalRamification

/-!
# Eisenstein minimal polynomials of uniformizers

In a finite DVR algebra with unchanged residue field, an integral power basis
whose generator is a uniformizer has an Eisenstein minimal polynomial.
-/

@[expose] public noncomputable section

open Polynomial IsLocalRing IsDiscreteValuationRing

namespace PowerBasis

variable {R S : Type*} [CommRing R] [IsDomain R] [IsDiscreteValuationRing R]
  [CommRing S] [IsDomain S] [IsDiscreteValuationRing S] [Algebra R S]
  [Module.Finite R S] [FaithfulSMul R S]

set_option backward.isDefEq.respectTransparency false in
/-- The reduction of a uniformizer's minimal polynomial is the monomial
of degree equal to the extension rank when the residue field is unchanged. -/
theorem minpolyMapResidueEqXPow (pb : PowerBasis R S) (hy : Irreducible pb.gen)
    (hres : ∀ s : S, ∃ r : R, residue S (algebraMap R S r) = residue S s) :
    (minpoly R pb.gen).map (residue R) = X ^ (minpoly R pb.gen).natDegree := by
  obtain ⟨π, hπ⟩ := exists_irreducible R
  let P := minpoly R pb.gen
  have hPm : P.Monic := minpoly.monic pb.isIntegral_gen
  have hv : addVal S (algebraMap R S π) = (P.natDegree : ℕ∞) := by
    rw [← finrankEqAddValMapUniformizer hres hπ, pb.finrank, pb.natDegree_minpoly]
  have hmem : pb.gen ^ P.natDegree ∈ (maximalIdeal R).map (algebraMap R S) := by
    rw [hπ.maximalIdeal_eq, Ideal.map_span, Set.image_singleton,
      Ideal.mem_span_singleton, ← addVal_le_iff_dvd, hv, hy.addVal_pow]
  have hz : Ideal.Quotient.mk ((maximalIdeal R).map (algebraMap R S))
      (aeval pb.gen (X ^ P.natDegree : R[X])) = 0 := by
    rw [map_pow, aeval_X, Ideal.Quotient.eq_zero_iff_mem]
    exact hmem
  have hd : P.map (residue R) ∣ X ^ P.natDegree := by
    have h := congrArg (pb.quotientEquivQuotientMinpolyMap (maximalIdeal R)) hz
    rw [pb.quotientEquivQuotientMinpolyMap_apply_mk, map_zero,
      Ideal.Quotient.eq_zero_iff_mem, Ideal.mem_span_singleton] at h
    simpa only [Polynomial.map_pow, map_X, P, IsLocalRing.residue] using h
  exact (eq_of_monic_of_dvd_of_natDegree_le (hPm.map _) (monic_X_pow _) hd
    (by rw [natDegree_X_pow, hPm.natDegree_map])).symm

/-- A uniformizer power-basis generator has an Eisenstein minimal polynomial
when the residue field is unchanged. -/
theorem minpolyEisensteinOfUniformizer (pb : PowerBasis R S) (hy : Irreducible pb.gen)
    (hres : ∀ s : S, ∃ r : R, residue S (algebraMap R S r) = residue S s) :
    (minpoly R pb.gen).IsEisensteinAt (maximalIdeal R) := by
  classical
  obtain ⟨π, hπ⟩ := exists_irreducible R
  let P := minpoly R pb.gen
  have hPm : P.Monic := minpoly.monic pb.isIntegral_gen
  have hn : 0 < P.natDegree := minpoly.natDegree_pos pb.isIntegral_gen
  have hred : P.map (residue R) = X ^ P.natDegree := pb.minpolyMapResidueEqXPow hy hres
  have hweak (i : ℕ) (hi : i < P.natDegree) : P.coeff i ∈ maximalIdeal R := by
    rw [← residue_eq_zero_iff, ← coeff_map, hred, coeff_X_pow, ite_eq_right hi.ne]
  have hd : C π ∣ P - X ^ P.natDegree := by
    rw [C_dvd_iff_dvd_coeff]
    intro i
    rw [coeff_sub, coeff_X_pow]
    rcases lt_trichotomy i P.natDegree with hi | hi | hi
    · simp only [ite_eq_right hi.ne, sub_zero]
      exact Ideal.mem_span_singleton.mp (hπ.maximalIdeal_eq ▸ hweak i hi)
    · simp [hi, hPm.coeff_natDegree]
    · simp [hi.ne', coeff_eq_zero_of_natDegree_lt hi]
  obtain ⟨H, hH⟩ := hd
  have hv : addVal S (algebraMap R S π) = (P.natDegree : ℕ∞) := by
    rw [← finrankEqAddValMapUniformizer hres hπ, pb.finrank, pb.natDegree_minpoly]
  have heval : -(pb.gen ^ P.natDegree) = algebraMap R S π * aeval pb.gen H := by
    have h := congrArg (aeval pb.gen) hH
    simpa [P, minpoly.aeval] using h
  have hvH : addVal S (aeval pb.gen H) = 0 := by
    have h := congrArg (addVal S) heval
    rw [AddValuation.map_neg, hy.addVal_pow, addVal_mul, hv] at h
    have htop : addVal S (aeval pb.gen H) ≠ ⊤ := by
      intro he
      simp [he] at h
    obtain ⟨v, hvv⟩ := ENat.ne_top_iff_exists.mp htop
    rw [← hvv, ← Nat.cast_add, ENat.natCast_inj] at h
    have hv0 : v = 0 := by omega
    simpa [hv0] using hvv.symm
  have hH0 : IsUnit (H.coeff 0) := by
    have hdiff : pb.gen ∣ aeval pb.gen H - algebraMap R S (H.coeff 0) := by
      simpa using _root_.map_dvd (aeval pb.gen) (X_dvd_sub_C (p := H))
    have hm : aeval pb.gen H - algebraMap R S (H.coeff 0) ∈ maximalIdeal S :=
      (maximalIdeal S).mem_of_dvd hdiff hy.not_isUnit
    have hr : residue S (aeval pb.gen H) = residue S (algebraMap R S (H.coeff 0)) :=
      sub_eq_zero.mp (by simpa using (residue_eq_zero_iff _).mpr hm)
    apply isUnit_of_map_unit (algebraMap R S)
    rw [← residue_ne_zero_iff_isUnit, ← hr]
    exact (residue_ne_zero_iff_isUnit _).mpr (addVal_eq_zero_iff.mp hvH)
  have hc : P.coeff 0 = π * H.coeff 0 := by
    have h := congrArg (fun f : R[X] => f.coeff 0) hH
    simpa [coeff_C_mul, hn.ne', hn.ne'.symm] using h
  have hirr : Irreducible (P.coeff 0) := by
    rw [hc]
    exact irreducible_mul_iff.mpr (Or.inl ⟨hπ, hH0⟩)
  refine hPm.isEisensteinAt_of_mem_of_notMem (maximalIdeal.isMaximal R).ne_top
    (fun {i} hi => hweak i hi) ?_
  intro hm
  rw [hπ.maximalIdeal_eq, Ideal.span_singleton_pow, Ideal.mem_span_singleton] at hm
  have hvbad := addVal_le_iff_dvd.mpr hm
  rw [hπ.addVal_pow, addVal_uniformizer hirr] at hvbad
  norm_num at hvbad

end PowerBasis
