/-
Copyright (c) 2026 krandder. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: krandder
-/
module

public import FLT.EllipticCurve.NTorsionRoots
public import Mathlib.RingTheory.AdjoinRoot
public import Mathlib.RingTheory.Flat.Basic

/-!
# The affine equation of multiplication on the x-line

The polynomial `Φ n - ξ ΨSq n` is monic of degree `n²`. It describes the
x-coordinate of the fiber over a finite value `ξ` of the multiplication map.
The fiber at infinity, needed for the torsion group scheme, requires an
additional chart; the affine equation alone does not construct that group scheme.
-/

@[expose] public section

open Polynomial
namespace WeierstrassCurve
variable {R : Type*} [CommRing R] (W : WeierstrassCurve R)

/-- The monic equation for the x-coordinate above the affine value `ξ` under
multiplication by `n`. -/
noncomputable def multiplicationFiberPolynomial (n : ℤ) (ξ : R) : R[X] :=
  W.Φ n - C ξ * W.ΨSq n

/-- The denominator term has smaller degree than the multiplication numerator. -/
lemma natDegree_C_mul_ΨSq_lt [Nontrivial R] {n : ℤ} (hn : n ≠ 0) (ξ : R) :
    (C ξ * W.ΨSq n).natDegree < (W.Φ n).natDegree := by
  apply lt_of_le_of_lt (natDegree_C_mul_le _ _)
  rw [W.natDegree_Φ]
  exact lt_of_le_of_lt (W.natDegree_ΨSq_le n)
    (Nat.sub_lt (pow_pos (Int.natAbs_pos.mpr hn) 2) (by decide))

/-- The affine multiplication-fiber equation is monic over any coefficient ring. -/
lemma monic_multiplicationFiberPolynomial {n : ℤ} (hn : n ≠ 0) (ξ : R) :
    (W.multiplicationFiberPolynomial n ξ).Monic := by
  nontriviality R
  exact (show (W.Φ n).Monic from W.leadingCoeff_Φ n).sub_of_left
    (degree_lt_degree (W.natDegree_C_mul_ΨSq_lt hn ξ))

/-- The affine multiplication-fiber equation has degree `n²`. -/
lemma natDegree_multiplicationFiberPolynomial [Nontrivial R] {n : ℤ} (hn : n ≠ 0)
    (ξ : R) : (W.multiplicationFiberPolynomial n ξ).natDegree = n.natAbs ^ 2 := by
  rw [multiplicationFiberPolynomial,
    natDegree_sub_eq_left_of_natDegree_lt (W.natDegree_C_mul_ΨSq_lt hn ξ), W.natDegree_Φ]

/-- The affine multiplication-fiber algebra has a power basis with `n²` elements. -/
noncomputable def multiplicationFiberBasis [Nontrivial R] {n : ℤ} (hn : n ≠ 0) (ξ : R) :
    Module.Basis (Fin (n.natAbs ^ 2)) R (AdjoinRoot (W.multiplicationFiberPolynomial n ξ)) :=
  ((AdjoinRoot.powerBasis' (W.monic_multiplicationFiberPolynomial hn ξ)).basis).reindex
    (finCongr (W.natDegree_multiplicationFiberPolynomial hn ξ))

/-- The affine multiplication-fiber algebra is finite over the coefficient ring. -/
theorem finite_multiplicationFiber {n : ℤ} (hn : n ≠ 0) (ξ : R) :
    Module.Finite R (AdjoinRoot (W.multiplicationFiberPolynomial n ξ)) :=
  (W.monic_multiplicationFiberPolynomial hn ξ).finite_adjoinRoot

/-- The affine multiplication-fiber algebra is flat, since its defining equation is monic. -/
theorem flat_multiplicationFiber {n : ℤ} (hn : n ≠ 0) (ξ : R) :
    Module.Flat R (AdjoinRoot (W.multiplicationFiberPolynomial n ξ)) := by
  let : Module.Free R (AdjoinRoot (W.multiplicationFiberPolynomial n ξ)) :=
    (W.monic_multiplicationFiberPolynomial hn ξ).free_adjoinRoot
  infer_instance

/-- The finite free affine multiplication-fiber algebra has rank `n²`. -/
theorem finrank_multiplicationFiber [Nontrivial R] {n : ℤ} (hn : n ≠ 0) (ξ : R) :
    Module.finrank R (AdjoinRoot (W.multiplicationFiberPolynomial n ξ)) = n.natAbs ^ 2 := by
  rw [Module.finrank_eq_card_basis (W.multiplicationFiberBasis hn ξ), Fintype.card_fin]

end WeierstrassCurve
