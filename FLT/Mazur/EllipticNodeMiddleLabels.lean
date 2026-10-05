/-
Copyright (c) 2026 krandder. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: krandder
-/
module

public import FLT.Mazur.EllipticNodeMiddleAddition

/-!
# Labels and actual classes of the middle component

Two witnesses at depth n/2 in an even model have smooth sum. This proves their
label addition law, annihilation by two and equality of their actual E/E₀
classes, without assuming that the label is a homomorphism elsewhere.
-/

@[expose] public section

namespace FLT.Mazur

open IsLocalRing WeierstrassCurve

variable {K : Type*} [Field K] {A : ValuationSubring K} {W : WeierstrassCurve A}
  {π : A} {n : ℕ} (D : SplitNodeDepth W π n)
  {P Q : (W.map (algebraMap A K)).toProjective.Point}

include D

/-- Two actual middle-depth points sum into E₀, including doubling and cancellation. -/
theorem NodePointCoordinates.smooth_add_of_middle
    (v : NodePointCoordinates A W π P) (w : NodePointCoordinates A W π Q)
    (hv : 2 * v.depth = n) (hw : 2 * w.depth = n) : SmoothReduction A W (P + Q) := by
  classical
  have hk : 0 < v.depth := by have := D.depth_pos; omega
  have he : v.depth = w.depth := by omega
  have hb := node_point_units_at_middle W D.uniformizer_ne_zero D.maximalIdeal_eq
    v.depth hk D.a₂_mem (by simpa only [hv] using D.a₃_mem)
    (by simpa only [hv] using D.a₄_mem) (by simpa only [hv] using D.a₆_mem)
    (by simpa only [hv] using D.a₆_not_mem) v.a v.b v.equation
  have hd := node_point_units_at_middle W D.uniformizer_ne_zero D.maximalIdeal_eq
    w.depth (by omega) D.a₂_mem (by simpa only [hw] using D.a₃_mem)
    (by simpa only [hw] using D.a₄_mem) (by simpa only [hw] using D.a₆_mem)
    (by simpa only [hw] using D.a₆_not_mem) w.a w.b w.equation
  have hs := smoothReduction_add_of_node_middle A W D.uniformizer_ne_zero D.maximalIdeal_eq
    v.depth hk v.a v.b w.a w.b v.nonsingular (by simpa only [he] using w.nonsingular)
    D.a₁_unit D.a₂_mem (Ideal.pow_le_pow_right (by omega) D.a₃_mem)
    (Ideal.pow_le_pow_right (by omega) D.a₄_mem)
    (Ideal.pow_le_self (Nat.ne_of_gt D.depth_pos) D.a₆_mem) hb.1 hd.2
  rw [toProjective_add] at hs
  rw [v.represents, w.represents]
  simpa only [he] using hs

/-- Addition of middle-depth points satisfies the label addition law. -/
theorem nodePointLabel_add_of_middle
    (v : NodePointCoordinates A W π P) (w : NodePointCoordinates A W π Q)
    (hv : 2 * v.depth = n) (hw : 2 * w.depth = n) :
    nodePointLabel D (P + Q) = nodePointLabel D P + nodePointLabel D Q := by
  have he : v.depth = w.depth := by omega
  rw [(nodePointLabel_eq_zero_iff D (P + Q)).mpr (v.smooth_add_of_middle D w hv hw),
    nodePointLabel_eq_of_coordinates D v, nodePointLabel_eq_of_coordinates D w,
    (nodeBranchLabel_middle hv v.b).1, (nodeBranchLabel_middle hw w.b).1, ← he]
  exact ((eq_neg_iff_add_eq_zero).mp (nodeBranchLabel_middle hv v.b).2).symm

/-- The double of a middle-depth point has smooth reduction. -/
theorem NodePointCoordinates.smooth_two_nsmul_of_middle
    (v : NodePointCoordinates A W π P) (hv : 2 * v.depth = n) :
    SmoothReduction A W (2 • P) := by
  simpa only [two_nsmul] using v.smooth_add_of_middle D v hv hv

/-- A middle-depth class is annihilated by two. -/
theorem NodePointCoordinates.two_nsmul_component_of_middle
    (v : NodePointCoordinates A W π P) (hv : 2 * v.depth = n) :
    2 • ellipticComponentHom A W P = 0 := by
  rw [nsmul_ellipticComponentHom_eq_zero_iff]
  exact v.smooth_two_nsmul_of_middle D hv

/-- All middle-depth witnesses represent the same actual component class. -/
theorem NodePointCoordinates.component_eq_of_middle
    (v : NodePointCoordinates A W π P) (w : NodePointCoordinates A W π Q)
    (hv : 2 * v.depth = n) (hw : 2 * w.depth = n) :
    ellipticComponentHom A W P = ellipticComponentHom A W Q := by
  have hs : ellipticComponentHom A W P + ellipticComponentHom A W Q = 0 := by
    rw [← map_add, ellipticComponentHom_eq_zero]
    exact v.smooth_add_of_middle D w hv hw
  have ht := w.two_nsmul_component_of_middle D hw
  rw [two_nsmul] at ht
  exact add_right_cancel (hs.trans ht.symm)

end FLT.Mazur
