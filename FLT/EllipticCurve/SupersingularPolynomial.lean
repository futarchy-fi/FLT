/-
Copyright (c) 2026 krandder. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: krandder
-/
module

public import FLT.EllipticCurve.PointReductionHom
public import Mathlib.RingTheory.DiscreteValuationRing.Basic
public import Mathlib.RingTheory.Polynomial.Eisenstein.Basic

/-!
# Division polynomials with trivial special-fiber torsion

Trivial geometric torsion makes the reduced division polynomial a nonzero constant.
When its leading coefficient is a uniformizer, reversing it gives an Eisenstein
polynomial, hence an irreducible polynomial over the fraction field.
-/

@[expose] public section

open Polynomial IsLocalRing
namespace WeierstrassCurve
variable {k : Type*} [Field k] [IsAlgClosed k] [DecidableEq k]
  (E : WeierstrassCurve k) [E.IsElliptic]

/-- Trivial geometric torsion forces the corresponding division polynomial to be a unit. -/
theorem isUnit_preΨ'_of_torsion_trivial (n : ℕ)
    (hno : ∀ P : E.toAffine.Point, n • P = 0 → P = 0) : IsUnit (E.preΨ' n) := by
  rw [Polynomial.isUnit_iff_degree_eq_zero]
  by_contra hd
  obtain ⟨x, hx⟩ := IsAlgClosed.exists_root (E.preΨ' n) hd
  obtain ⟨y, hy⟩ := E.exists_equation_y x
  have h : E.toAffine.Nonsingular x y := Affine.equation_iff_nonsingular.mp hy
  have hψ : (E.ΨSq n).IsRoot x := by
    simp only [ΨSq_ofNat, IsRoot, eval_mul, eval_pow, hx.eq_zero, zero_pow two_ne_zero, zero_mul]
  exact Affine.Point.some_ne_zero h (hno (.some _ _ h) (E.nsmul_eq_zero_of_isRoot_ΨSq h n hψ))
end WeierstrassCurve

namespace Polynomial

variable {R : Type*} [CommRing R] [IsLocalRing R]
/-- A polynomial with unit reduction and leading coefficient of valuation one has
Eisenstein reverse. -/
theorem isEisensteinAt_reverse_of_isUnit_reduction (f : R[X])
    (hu : IsUnit (f.map (residue R))) (hl : f.leadingCoeff ∉ maximalIdeal R ^ 2) :
    f.reverse.IsEisensteinAt (maximalIdeal R) := by
  have hd : (f.map (residue R)).natDegree = 0 := natDegree_eq_zero_of_isUnit hu
  have he : f.map (residue R) = C (residue R (f.coeff 0)) := by
    simpa only [coeff_map] using eq_C_of_natDegree_eq_zero hd
  have hc : IsUnit (f.coeff 0) := (residue_ne_zero_iff_isUnit _).mp (by
    intro hz
    exact hu.ne_zero (by rw [he, hz, C_0]))
  have ht : f.natTrailingDegree = 0 := by
    rw [natTrailingDegree_eq_zero]
    exact Or.inr hc.ne_zero
  refine ⟨?_, ?_, ?_⟩
  · rw [reverse_leadingCoeff, trailingCoeff, ht]
    simpa using hc
  · intro i hi
    rw [reverse_natDegree, ht, Nat.sub_zero] at hi
    rw [coeff_reverse, revAt_le hi.le]
    apply (residue_eq_zero_iff _).mp
    have hp : f.natDegree - i ≠ 0 := (Nat.sub_pos_of_lt hi).ne'
    have hh := congrArg (fun g : (ResidueField R)[X] => g.coeff (f.natDegree - i)) he
    simpa only [coeff_map, coeff_C, ite_eq_right hp] using hh
  · simpa only [coeff_zero_reverse] using hl
end Polynomial

namespace WeierstrassCurve
variable (R K : Type*) [CommRing R] [IsDomain R] [IsDiscreteValuationRing R]
  [Field K] [Algebra R K] [IsFractionRing R K] [CharZero R]
  (W : WeierstrassCurve R) [(W.map (residue R)).IsElliptic]
  [DecidableEq (AlgebraicClosure (ResidueField R))]
local notation "κ" => ResidueField R
local notation "κbar" => AlgebraicClosure κ

/-- If geometric special-fiber torsion is trivial and its order is a uniformizer,
the reversed odd division polynomial is irreducible over the fraction field. -/
theorem irreducible_reverse_preΨ'_of_torsion_trivial (n : ℕ) (hn : 2 < n)
    (ho : ¬ Even n) (hp : (n : R) ∉ maximalIdeal R ^ 2)
    (hno : ∀ P : ((W.map (residue R)).map (algebraMap κ κbar)).toAffine.Point,
      n • P = 0 → P = 0) :
    Irreducible ((W.preΨ' n).reverse.map (algebraMap R K)) := by
  classical
  have hu : IsUnit ((W.preΨ' n).map (residue R)) := by
    have hh := isUnit_preΨ'_of_torsion_trivial
      ((W.map (residue R)).map (algebraMap κ κbar)) n hno
    rw [map_preΨ', map_preΨ', Polynomial.isUnit_iff_degree_eq_zero, degree_map] at hh
    exact Polynomial.isUnit_iff_degree_eq_zero.mpr hh
  have hnc : (n : R) ≠ 0 := Nat.cast_ne_zero.mpr (by omega)
  have hl : (W.preΨ' n).leadingCoeff = n := by simp only [W.leadingCoeff_preΨ' hnc, ho, ite_false]
  have he := Polynomial.isEisensteinAt_reverse_of_isUnit_reduction (W.preΨ' n) hu
    (by rwa [hl])
  have hlead : IsUnit (W.preΨ' n).reverse.leadingCoeff := by simpa using he.leading
  have hprim : (W.preΨ' n).reverse.IsPrimitive := by
    intro c hc
    exact isUnit_of_dvd_unit
      ((C_dvd_iff_dvd_coeff _ _).mp hc (W.preΨ' n).reverse.natDegree) hlead
  have hcoeff : (W.preΨ' n).coeff 0 ≠ 0 := by
    intro hz
    have hconstant := eq_C_of_natDegree_eq_zero (natDegree_eq_zero_of_isUnit hu)
    apply hu.ne_zero
    simpa only [coeff_map, hz, map_zero, C_0] using hconstant
  have ht : (W.preΨ' n).natTrailingDegree = 0 := by
    rw [natTrailingDegree_eq_zero]
    exact Or.inr hcoeff
  apply hprim.irreducible_iff_irreducible_map_fraction_map.mp
  apply he.irreducible inferInstance hprim
  rw [reverse_natDegree, ht, Nat.sub_zero]
  exact W.natDegree_preΨ'_pos hn hnc
end WeierstrassCurve

