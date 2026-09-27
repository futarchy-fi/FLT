/-
Copyright (c) 2026 krandder. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: krandder
-/
module

public import FLT.EllipticCurve.FunctionFieldOrder
public import FLT.EllipticCurve.TorsionPairingBilinear
/-!
# Alternation of the torsion pairing

The product of translates of a multiplication root along a division point
has zero divisor. Its constancy forces the diagonal translation ratio to be one.
-/

@[expose] public section

open scoped nonZeroDivisors WeierstrassCurve.Affine
namespace WeierstrassCurve.Affine.FunctionField
variable {F : Type*} [Field F] [IsAlgClosed F] [DecidableEq F]
  (W : Affine F) [W.IsElliptic]

/-- The torsion function in root data has divisor n[T] - n[O]. -/
theorem TorsionRoot.pointOrder_f {n : ℕ} {hn : n ≠ 0} {T : W.Point}
    (r : TorsionRoot W n hn T) (hT : n • T = 0) (P : W.Point) :
    pointOrder r.f P = (if T = P then (n : ℤ) else 0) -
      (if (0 : W.Point) = P then (n : ℤ) else 0) := by
  cases T with
  | zero =>
    have hf : FractionalIdeal.spanSingleton W.CoordinateRing⁰ (1 : W.FunctionField) =
        FractionalIdeal.spanSingleton W.CoordinateRing⁰ r.f := by
      rw [r.hf]; simp [Point.fractionalIdeal]
    obtain ⟨c, hc, he⟩ := exists_eq_const_mul_of_span_eq hf
    rw [mul_one] at he
    rw [he, pointOrder_const W hc]
    change 0 = (if (0 : W.Point) = P then (n : ℤ) else 0) - _
    exact (sub_self _).symm
  | some x y h =>
    obtain ⟨f, hf0, hf⟩ := Point.exists_torsionFunction h n hT
    have he : FractionalIdeal.spanSingleton W.CoordinateRing⁰
        (algebraMap W.CoordinateRing W.FunctionField f) =
        FractionalIdeal.spanSingleton W.CoordinateRing⁰ r.f := by
      rw [r.hf, Point.fractionalIdeal_some, CoordinateRing.XYIdeal'_eq,
        ← FractionalIdeal.coeIdeal_pow, hf, FractionalIdeal.coeIdeal_span_singleton]
    obtain ⟨c, hc, he⟩ := exists_eq_const_mul_of_span_eq he
    rw [he, pointOrder_mul ((map_ne_zero _).mpr hc)
      ((map_ne_zero_iff _ (IsFractionRing.injective _ _)).mpr hf0),
      pointOrder_const W hc, zero_add, pointOrder_torsionFunction h hf0 hf]
    simp only [Finsupp.coe_sub, Pi.sub_apply, Finsupp.single_apply]
    rfl

/-- A multiplication root has simple zeros and poles on the two multiplication fibers. -/
theorem TorsionRoot.pointOrder_g {n : ℕ} (hn : n ≠ 0) (hchar : (n : F) ≠ 0)
    {T : W.Point} (r : TorsionRoot W n hn T) (hT : n • T = 0) (P : W.Point) :
    pointOrder r.g P = (if T = n • P then 1 else 0) -
      (if (0 : W.Point) = n • P then 1 else 0) := by
  have he := congrArg (fun f => pointOrder f P) r.hg
  rw [pointOrder_pow W r.hg0, pointOrder_nsmulPullback W hn hchar,
    r.pointOrder_f W hT] at he
  apply mul_left_cancel₀ (show (n : ℤ) ≠ 0 by exact_mod_cast hn)
  convert he using 1
  split_ifs <;> ring

/-- The product of translates of a root along a division point is constant. -/
theorem TorsionRoot.exists_const_cyclicProduct {n : ℕ} (hn : n ≠ 0)
    (hchar : (n : F) ≠ 0) {T : W.Point} (r : TorsionRoot W n hn T)
    (hT : n • T = 0) (Q : W.Point) (hQ : n • Q = T) :
    ∃ c : F, c ≠ 0 ∧ algebraMap F W.FunctionField c =
      ∏ i ∈ Finset.range n, translationPullback W (-(i • Q)) r.g := by
  apply exists_const_of_pointOrder_eq_zero W
    (Finset.prod_ne_zero_iff.mpr (fun i _ => (map_ne_zero _).mpr r.hg0))
  intro P
  rw [pointOrder_prod W _ _ (fun i _ => (map_ne_zero _).mpr r.hg0)]
  have hi (i : ℕ) : pointOrder (translationPullback W (-(i • Q)) r.g) P =
      (if (i + 1) • T = n • P then (1 : ℤ) else 0) -
        (if i • T = n • P then 1 else 0) := by
    rw [pointOrder_translationPullback, r.pointOrder_g W hn hchar hT,
      nsmul_add, smul_neg, smul_comm n i Q, hQ]
    simp only [← sub_eq_add_neg, eq_sub_iff_add_eq, zero_add, succ_nsmul']
  simp_rw [hi]
  rw [Finset.sum_range_sub (fun i => if i • T = n • P then (1 : ℤ) else 0)]
  simp [hT]

/-- A root is fixed by translation by its supporting torsion point. -/
theorem TorsionRoot.translation_self {n : ℕ} (hn : n ≠ 0) (hchar : (n : F) ≠ 0)
    {T : W.Point} (r : TorsionRoot W n hn T) (hT : n • T = 0) :
    translationPullback W T r.g = r.g := by
  obtain ⟨Q, hQ⟩ := Point.exists_nsmul_eq_of_torsion W hchar T hT
  obtain ⟨c, hc, he⟩ := r.exists_const_cyclicProduct W hn hchar hT Q hQ
  let a (i : ℕ) := translationPullback W (-(i • Q)) r.g
  have hshift (i : ℕ) : translationPullback W (-Q) (a i) = a (i + 1) := by
    change ((translationPullback W (-Q)).comp
      (translationPullback W (-(i • Q)))) r.g = _
    rw [translationPullback_add]
    congr 2
    simp only [succ_nsmul', neg_add_rev]
    abel
  change algebraMap F W.FunctionField c = ∏ i ∈ Finset.range n, a i at he
  have hinv : (∏ i ∈ Finset.range n, a (i + 1)) = ∏ i ∈ Finset.range n, a i := by
    have hh := congrArg (translationPullback W (-Q)) he
    rw [AlgHom.commutes, map_prod] at hh
    simpa only [hshift, he] using hh.symm
  have hends : a n = a 0 := by
    have hh := (Finset.prod_range_succ a n).symm.trans (Finset.prod_range_succ' a n)
    rw [hinv] at hh
    exact mul_left_cancel₀
      (Finset.prod_ne_zero_iff.mpr (fun i _ => (map_ne_zero _).mpr r.hg0)) hh
  have hneg : translationPullback W (-T) r.g = r.g := by
    simpa [a, hQ, translationPullback_zero] using hends
  have hh := congrArg (translationPullback W T) hneg
  change ((translationPullback W T).comp (translationPullback W (-T))) r.g = _ at hh
  rw [translationPullback_add, add_neg_cancel, translationPullback_zero] at hh
  exact hh.symm

/-- The torsion pairing is alternating. -/
theorem torsionPairing_self {n : ℕ} (hn : n ≠ 0) (hchar : (n : F) ≠ 0)
    (T : Point.torsionKernel W n) : torsionPairing W hn hchar T T = 0 := by
  apply Additive.toMul.injective
  apply rootsOfUnity.coe_injective
  apply (algebraMap F W.FunctionField).injective
  change algebraMap F W.FunctionField ((torsionPairing W hn hchar T T).toMul.val : F) =
    algebraMap F W.FunctionField 1
  let r := chosenTorsionRoot W hn hchar T
  rw [torsionPairing_eq_ratio W hn hchar T T r,
    r.translation_self W hn hchar T.property, div_self r.hg0, map_one]

/-- Interchanging the arguments negates the additive torsion pairing. -/
theorem torsionPairing_swap {n : ℕ} (hn : n ≠ 0) (hchar : (n : F) ≠ 0)
    (S T : Point.torsionKernel W n) :
    torsionPairing W hn hchar S T = -torsionPairing W hn hchar T S := by
  have he := torsionPairing_self W hn hchar (S + T)
  rw [torsionPairing_add_left, torsionPairing_add_right, torsionPairing_add_right,
    torsionPairing_self, torsionPairing_self, zero_add, add_zero] at he
  exact eq_neg_of_add_eq_zero_left he

end WeierstrassCurve.Affine.FunctionField
