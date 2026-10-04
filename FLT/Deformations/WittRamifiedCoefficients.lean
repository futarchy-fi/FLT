/-
Copyright (c) 2026 krandder. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: krandder
-/
module

public import FLT.Deformations.EisensteinCoefficientObject
public import FLT.Deformations.WittCoefficientResidue

/-!
# Explicit ramified Witt coefficient targets

For every positive e, adjoin a root of X^e - p to W(k). The resulting
characteristic-zero domain is finite free over W(k), complete, and has
the specified residue field. No lift of a residual representation is asserted.
-/

@[expose] public noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open Polynomial IsLocalRing
open scoped Deformation.WittCoefficients
namespace Deformation.WittCoefficients
variable (p : ℕ) [Fact p.Prime] (k : Type) [Field k] [CharP k p] [Finite k]
  (e : ℕ) [NeZero e]
local notation "W" => WittVector p k

/-- The explicit equation for the ramified coefficient uniformizer. -/
def ramifiedPolynomial : W[X] := X ^ e - C (p : W)

omit [CharP k p] [Finite k] in
/-- The defining equation is monic. -/
theorem ramifiedPolynomial_monic : (ramifiedPolynomial p k e).Monic :=
  monic_X_pow_sub_C _ (NeZero.ne e)

omit [CharP k p] [Finite k] [NeZero e] in
/-- The extension degree is the chosen positive integer. -/
theorem ramifiedPolynomial_degree : (ramifiedPolynomial p k e).natDegree = e :=
  natDegree_X_pow_sub_C

/-- The equation is Eisenstein at the actual maximal ideal of W(k). -/
theorem ramifiedPolynomial_eisenstein :
    (ramifiedPolynomial p k e).IsEisensteinAt (maximalIdeal W) := by
  apply (ramifiedPolynomial_monic p k e).isEisensteinAt_of_mem_of_notMem
    (maximalIdeal.isMaximal W).ne_top
  · intro n hn
    rw [ramifiedPolynomial_degree] at hn
    simp only [ramifiedPolynomial, coeff_sub, coeff_X_pow, coeff_C,
      ite_eq_right (Nat.ne_of_lt hn), zero_sub]
    split_ifs
    · exact (maximalIdeal W).neg_mem ((WittVector.irreducible p).not_isUnit)
    · exact (maximalIdeal W).neg_mem (Ideal.zero_mem _)
  · simp only [ramifiedPolynomial, coeff_sub, coeff_X_pow, coeff_C_zero,
      ite_eq_right (Ne.symm (NeZero.ne e)), zero_sub, Ideal.neg_mem_iff]
    rw [maximalIdeal_eq, Ideal.span_singleton_pow, Ideal.mem_span_singleton]
    intro h
    have hdiv : (p : W) * p ∣ (p : W) * 1 := by simpa [pow_two] using h
    exact (WittVector.irreducible p).not_isUnit
      (isUnit_of_dvd_one ((mul_dvd_mul_iff_left (WittVector.p_nonzero p k)).mp hdiv))

local instance : Fact (ramifiedPolynomial p k e).Monic :=
  ⟨ramifiedPolynomial_monic p k e⟩
local instance : Fact (0 < (ramifiedPolynomial p k e).natDegree) :=
  ⟨by rw [ramifiedPolynomial_degree]; exact NeZero.pos e⟩
local instance : Fact ((ramifiedPolynomial p k e).IsEisensteinAt (maximalIdeal W)) :=
  ⟨ramifiedPolynomial_eisenstein p k e⟩

/-- A concrete ramified characteristic-zero coefficient object for every positive e. -/
def ramifiedObject : ProartinianCat W :=
  EisensteinCoefficients.object W (ramifiedPolynomial p k e)

/-- The constructed target is a domain. -/
theorem ramifiedObject_isDomain : IsDomain (ramifiedObject p k e) :=
  EisensteinCoefficients.object_isDomain W (ramifiedPolynomial p k e)

/-- Characteristic zero is proved from the original Witt scalar embedding. -/
theorem ramifiedObject_charZero : CharZero (ramifiedObject p k e) :=
  EisensteinCoefficients.object_charZero W (ramifiedPolynomial p k e)

/-- The target is finite over the original Witt ring. -/
theorem ramifiedObject_finite : Module.Finite W (ramifiedObject p k e) :=
  EisensteinCoefficients.object_finite W (ramifiedPolynomial p k e)

/-- The target is free over the original Witt ring. -/
theorem ramifiedObject_free : Module.Free W (ramifiedObject p k e) :=
  (ramifiedPolynomial_monic p k e).free_adjoinRoot

/-- The finite free coefficient extension has exactly the chosen rank. -/
theorem ramifiedObject_finrank : Module.finrank W (ramifiedObject p k e) = e :=
  (AdjoinRoot.powerBasis' (ramifiedPolynomial_monic p k e)).finrank.trans
    (ramifiedPolynomial_degree p k e)

/-- The specified residue-field identification, with the original Witt scalar action. -/
def ramifiedResidueEquiv : ResidueField (ramifiedObject p k e) ≃+* k :=
  (IsResidueAlgebra.algEquiv W (ramifiedObject p k e)).symm.toRingEquiv.trans
    (residueEquiv p k)

/-- The fixed residue identification agrees with reduction of the original coefficients. -/
theorem ramifiedResidueEquiv_scalar (x : W) :
    ramifiedResidueEquiv p k e
      (residue (ramifiedObject p k e) (algebraMap W (ramifiedObject p k e) x)) =
      WittVector.constantCoeff x := by
  change residueEquiv p k ((IsResidueAlgebra.algEquiv W
    (ramifiedObject p k e)).symm (algebraMap W (ResidueField (ramifiedObject p k e)) x)) = _
  rw [AlgEquiv.commutes]
  exact residueEquiv_residue p k x

/-- The distinguished integral root. -/
def ramifiedUniformizer : ramifiedObject p k e :=
  AdjoinRoot.root (ramifiedPolynomial p k e)

/-- The root satisfies the actual ramification equation in characteristic zero. -/
theorem ramifiedUniformizer_pow :
    ramifiedUniformizer p k e ^ e = (p : ramifiedObject p k e) := by
  have h := AdjoinRoot.eval₂_root (ramifiedPolynomial p k e)
  simpa only [ramifiedPolynomial, eval₂_sub, eval₂_pow, eval₂_X, eval₂_C, eval₂_natCast,
    map_natCast, sub_eq_zero, ramifiedUniformizer] using h

end Deformation.WittCoefficients
