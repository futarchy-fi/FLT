/-
Copyright (c) 2026 krandder. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: krandder
-/
module

public import Mathlib.AlgebraicGeometry.EllipticCurve.Affine.Point
public import Mathlib.FieldTheory.IsAlgClosed.AlgebraicClosure
public import Mathlib.FieldTheory.IsSepClosed
public import Mathlib.SetTheory.Cardinal.NatCard

/-!
# The cardinality of two-torsion

In characteristic different from two, the cubic two-torsion polynomial is
separable. Its three roots over a separably closed field give the three
nonzero two-torsion points.
-/

@[expose] public section

open Polynomial

namespace WeierstrassCurve

variable {k : Type*} [Field k] (E : WeierstrassCurve k) [E.IsElliptic]

/-- The two-torsion polynomial of an elliptic curve is separable in
characteristic different from two. -/
theorem separable_twoTorsionPolynomial (h2 : (2 : k) ≠ 0) :
    E.twoTorsionPolynomial.toPoly.Separable := by
  have h4 : E.twoTorsionPolynomial.a ≠ 0 := by
    change (4 : k) ≠ 0
    convert pow_ne_zero 2 h2 using 1
    norm_num
  have hs := IsAlgClosed.splits (E.twoTorsionPolynomial.toPoly.map
    (algebraMap k (AlgebraicClosure k)))
  apply (Polynomial.nodup_aroots_iff_of_splits
    (E.twoTorsionPolynomial.ne_zero_of_a_ne_zero h4) hs).mp
  have hn := (E.twoTorsionPolynomial.discr_ne_zero_iff_roots_nodup h4 hs).mp
    (E.twoTorsionPolynomial_discr_ne_zero_of_isElliptic h2.isUnit)
  simpa only [Cubic.roots, Cubic.map_toPoly, Polynomial.aroots] using hn

/-- Over a separably closed field of characteristic different from two,
the two-torsion polynomial has three distinct roots. -/
theorem card_twoTorsionPolynomial_roots [IsSepClosed k] (h2 : (2 : k) ≠ 0) :
    Nat.card (E.twoTorsionPolynomial.toPoly.rootSet k) = 3 := by
  have hs := E.separable_twoTorsionPolynomial h2
  rw [Nat.card_eq_fintype_card,
    Polynomial.card_rootSet_eq_natDegree hs (by
      simpa using IsSepClosed.splits_of_separable _ hs)]
  apply Cubic.natDegree_of_a_ne_zero
  change (4 : k) ≠ 0
  convert pow_ne_zero 2 h2 using 1
  norm_num

/-- The x-coordinate identifies nonzero two-torsion points with roots of
the two-torsion polynomial. -/
noncomputable def nonzeroTwoTorsionEquivRoots [DecidableEq k] (h2 : (2 : k) ≠ 0) :
    {P : E.toAffine.Point // 2 • P = 0 ∧ P ≠ 0} ≃
      E.twoTorsionPolynomial.toPoly.rootSet k := by
  have hp : E.twoTorsionPolynomial.toPoly ≠ 0 := (E.separable_twoTorsionPolynomial h2).ne_zero
  let f : {P : E.toAffine.Point // 2 • P = 0 ∧ P ≠ 0} →
      E.twoTorsionPolynomial.toPoly.rootSet k := fun P =>
    ⟨P.val.xRep 0, by
      apply (Polynomial.mem_rootSet_of_ne hp).mpr
      obtain ⟨P, ht, hn⟩ := P
      cases P with
      | zero => exact (hn rfl).elim
      | some x y h =>
        simpa only [Polynomial.aeval_def, Algebra.algebraMap_self, eval₂_id,
          Polynomial.IsRoot, Affine.Point.xRep_some,
          Matrix.cons_val_zero] using
          Affine.Point.isRoot_twoTorsionPolynomial_of_add_self h (by
            simpa only [two_nsmul] using ht)⟩
  apply Equiv.ofBijective f
  constructor
  · intro P Q hPQ
    have hx : P.val.xRep = Q.val.xRep := by
      have he := congrArg Subtype.val hPQ
      obtain ⟨P, ht, hn⟩ := P
      obtain ⟨Q, hu, hm⟩ := Q
      cases P with
      | zero => exact (hn rfl).elim
      | some x y h =>
        cases Q with
        | zero => exact (hm rfl).elim
        | some x' y' h' =>
          change x = x' at he
          simp only [Affine.Point.xRep_some, he]
    apply Subtype.ext
    rcases Affine.Point.eq_or_eq_neg_of_xRep_eq_xRep hx with he | he
    · exact he
    · have hneg : -Q.val = Q.val := neg_eq_of_add_eq_zero_left (by
        simpa only [two_nsmul] using Q.property.1)
      exact he.trans hneg
  · intro x
    have hx : E.twoTorsionPolynomial.toPoly.IsRoot x.val := by
      simpa only [Polynomial.aeval_def, Algebra.algebraMap_self, eval₂_id,
        Polynomial.IsRoot] using
        (Polynomial.mem_rootSet_of_ne hp).mp x.property
    obtain ⟨y, hy, ht⟩ :=
      (Affine.Point.isRoot_twoTorsionPolynomial_iff (W := E) ⟨h2⟩ E.isUnit_Δ.ne_zero x.val).mp hx
    refine ⟨⟨Affine.Point.some x.val y hy, ?_, Affine.Point.some_ne_zero hy⟩, ?_⟩
    · simpa only [two_nsmul] using ht
    · exact Subtype.ext rfl

/-- The kernel of multiplication by two has four points over a separably
closed field of characteristic different from two. -/
theorem card_two_torsion [DecidableEq k] [IsSepClosed k] (h2 : (2 : k) ≠ 0) :
    Nat.card {P : E.toAffine.Point // 2 • P = 0} = 4 := by
  classical
  let T := {P : E.toAffine.Point // 2 • P = 0}
  let z : T := ⟨0, by simp⟩
  let e : {P : T // P ≠ z} ≃ {P : E.toAffine.Point // 2 • P = 0 ∧ P ≠ 0} :=
    { toFun := fun P => ⟨P.val.val, P.val.property, fun h => P.property (Subtype.ext h)⟩
      invFun := fun P => ⟨⟨P.val, P.property.1⟩, fun h =>
        P.property.2 (congrArg Subtype.val h)⟩
      left_inv := fun _ => rfl
      right_inv := fun _ => rfl }
  let er := e.trans (E.nonzeroTwoTorsionEquivRoots h2)
  let : Fintype {P : T // P ≠ z} := Fintype.ofEquiv _ er.symm
  change Nat.card T = 4
  rw [← Nat.card_congr (Equiv.optionSubtypeNe z), Nat.card_eq_fintype_card,
    Fintype.card_option, ← Nat.card_eq_fintype_card,
    Nat.card_congr er, E.card_twoTorsionPolynomial_roots h2]

end WeierstrassCurve
