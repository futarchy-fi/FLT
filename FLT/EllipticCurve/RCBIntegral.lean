/-
Copyright (c) 2026 krandder. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: krandder
-/
module

public import FLT.EllipticCurve.RCBPoints
public import FLT.EllipticCurve.OddTorsionModel
/-!
# An invertible addition coordinate over good reduction

The RCB Y-coordinate is a unit on the tensor square of the odd multiplication
fibre over an integral nonzero two-torsion point. The maximal-ideal argument
works over arbitrary rings and does not discard nilpotents.
-/

@[expose] public section

open Polynomial
namespace WeierstrassCurve.RCB
variable {R : Type*} [CommRing R] (W : WeierstrassCurve R) [W.IsShortNF]
/-- On the odd multiplication fibre above integral two-torsion, the RCB
Y-coordinate is a unit over every good-reduction coefficient ring, including
nonreduced algebras. The proof checks every maximal residue field. -/
theorem isUnit_addY_of_multiplicationFiber (hΔ : IsUnit W.Δ) (h2 : IsUnit (2 : R))
    {n : ℕ} (hn : Odd n) (ξ x1 y1 x2 y2 : R)
    (hT : W.toAffine.Equation ξ 0)
    (h1 : W.toAffine.Equation x1 y1) (h2p : W.toAffine.Equation x2 y2)
    (hx1 : (W.multiplicationFiberPolynomial n ξ).eval x1 = 0)
    (hx2 : (W.multiplicationFiberPolynomial n ξ).eval x2 = 0) :
    IsUnit (addY W.a₄ W.a₆ x1 y1 1 x2 y2 1) := by
  classical
  let : W.IsElliptic := ⟨hΔ⟩
  by_contra hu
  obtain ⟨M, hM, hm⟩ := exists_max_ideal_of_mem_nonunits (mem_nonunits_iff.mpr hu)
  let : M.IsMaximal := hM
  let : Field (R ⧸ M) := Ideal.Quotient.field M
  let f := Ideal.Quotient.mk M
  let E := W.map f
  let : E.IsShortNF := ⟨by simp [E, map],
    by simp [E, map, a₂_of_isShortNF], by simp [E, map]⟩
  let : NeZero (2 : R ⧸ M) := ⟨by simpa only [map_ofNat] using (h2.map f).ne_zero⟩
  have ht : E.toAffine.Nonsingular (f ξ) 0 :=
    Affine.equation_iff_nonsingular.mp (by simpa only [map_zero] using hT.map f)
  have hp1 : E.toAffine.Nonsingular (f x1) (f y1) :=
    Affine.equation_iff_nonsingular.mp (h1.map f)
  have hp2 : E.toAffine.Nonsingular (f x2) (f y2) :=
    Affine.equation_iff_nonsingular.mp (h2p.map f)
  have htt : 2 • Affine.Point.some (f ξ) 0 ht = 0 := by
    rw [two_nsmul]
    apply Affine.Point.add_self_of_Y_eq
    simp [Affine.negY, E, map]
  have hp1n : n • Affine.Point.some _ _ hp1 = Affine.Point.some _ _ ht := by
    apply (E.isRoot_multiplicationFiberPolynomial_iff_nsmul_eq_two_torsion hp1 ht htt n).mp
    simp only [E, map_multiplicationFiberPolynomial, Polynomial.IsRoot,
      eval_map_apply, hx1, map_zero]
  have hp2n : n • Affine.Point.some _ _ hp2 = Affine.Point.some _ _ ht := by
    apply (E.isRoot_multiplicationFiberPolynomial_iff_nsmul_eq_two_torsion hp2 ht htt n).mp
    simp only [E, map_multiplicationFiberPolynomial, Polynomial.IsRoot,
      eval_map_apply, hx2, map_zero]
  have hy := addY_ne_zero_of_odd_sum_diff E hp1 hp2 hn
    (by rw [nsmul_add, hp1n, hp2n]; simpa only [two_nsmul] using htt)
    (by rw [nsmul_sub, hp1n, hp2n, sub_self])
  apply hy
  have he : f (addY W.a₄ W.a₆ x1 y1 1 x2 y2 1) = 0 :=
    Ideal.Quotient.eq_zero_iff_mem.mpr hm
  simpa only [E, map, addY, map_add, map_sub, map_mul, map_pow, map_one,
    map_ofNat] using he
end WeierstrassCurve.RCB
