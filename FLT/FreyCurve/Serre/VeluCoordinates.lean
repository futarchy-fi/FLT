/-
Copyright (c) 2026 krandder. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: krandder
-/
module

public import FLT.FreyCurve.Serre.VeluMap

/-!
# Rational coordinate expressions for Vélu's map

Pairing a kernel point with its inverse eliminates its y-coordinate. These identities
express both coordinate sums as rational functions away from the kernel, for a general
Weierstrass equation in characteristic different from two. They do not yet prove
that the candidate target equation is satisfied, that it is nonsingular, or additivity.

The general pair identities are derived directly from Mathlib's affine group law.
For the short Weierstrass specialization see Andrew Sutherland, MIT 18.783 (Fall 2025),
Lecture 5, Theorem 5.15:
https://ocw.mit.edu/courses/18-783-elliptic-curves-fall-2025/mit18_783_f25_lec05.pdf
-/

@[expose] public section


open scoped BigOperators WeierstrassCurve.Affine
namespace WeierstrassCurve.Velu
variable {K : Type*} [Field K] [DecidableEq K]

/-- Paired translates eliminate the y-coordinate from the x-map. -/
theorem xCoord_add_pair (E : WeierstrassCurve K) {x y u v : K}
    (hP : E.toAffine.Nonsingular x y) (hQ : E.toAffine.Nonsingular u v)
    (hxu : x ≠ u) :
    xCoord (Affine.Point.some x y hP + Affine.Point.some u v hQ) +
      xCoord (Affine.Point.some x y hP - Affine.Point.some u v hQ) - 2 * u =
      (6 * u ^ 2 + E.b₂ * u + E.b₄) / (x - u) +
        (4 * u ^ 3 + E.b₂ * u ^ 2 + 2 * E.b₄ * u + E.b₆) / (x - u) ^ 2 := by
  simp only [sub_eq_add_neg (Affine.Point.some x y hP), Affine.Point.neg_some,
    Affine.Point.add_of_X_ne hxu, xCoord, Affine.addX_of_X_ne hxu]
  have hp := (Affine.equation_iff _ _).mp hP.1
  have hq := (Affine.equation_iff _ _).mp hQ.1
  dsimp [Affine.negY, b₂, b₄, b₆]
  field_simp
  linear_combination 2 * hp + 2 * hq


/-- Outside the kernel, an affine x-coordinate differs from every nonzero kernel x-coordinate. -/
theorem xCoord_ne_of_not_mem (E : WeierstrassCurve K) (G : AddSubgroup E.toAffine.Point)
    {x y : K} (hP : E.toAffine.Nonsingular x y)
    (hPG : Affine.Point.some x y hP ∉ G) {u v : K}
    (hQ : E.toAffine.Nonsingular u v) (hQG : Affine.Point.some u v hQ ∈ G) :
    x ≠ u := by
  intro h
  have hx : (Affine.Point.some x y hP).xRep = (Affine.Point.some u v hQ).xRep := by
    simp only [Affine.Point.xRep_some, h]
  rcases Affine.Point.eq_or_eq_neg_of_xRep_eq_xRep hx with heq | heq
  · exact hPG (heq ▸ hQG)
  · exact hPG (heq ▸ G.neg_mem hQG)

/-- The x-map as a sum of rational functions of x; the identity contributes x. -/
theorem xMap_eq_sum_rational [NeZero (2 : K)] (E : WeierstrassCurve K)
    (G : AddSubgroup E.toAffine.Point) [Fintype G] {x y : K}
    (hP : E.toAffine.Nonsingular x y) (hPG : Affine.Point.some x y hP ∉ G) :
    xMap E G (.some x y hP) =
      ∑ Q : G, if Q = 0 then x else
        tTerm E (xCoord Q.val) / (x - xCoord Q.val) +
          (4 * xCoord Q.val ^ 3 + E.b₂ * xCoord Q.val ^ 2 +
            2 * E.b₄ * xCoord Q.val + E.b₆) / (2 * (x - xCoord Q.val) ^ 2) := by
  classical
  let f (Q : G) := xCoord (Affine.Point.some x y hP + Q.val) - xCoord Q.val
  let r (Q : G) := if Q = 0 then x else
    tTerm E (xCoord Q.val) / (x - xCoord Q.val) +
      (4 * xCoord Q.val ^ 3 + E.b₂ * xCoord Q.val ^ 2 +
        2 * E.b₄ * xCoord Q.val + E.b₆) / (2 * (x - xCoord Q.val) ^ 2)
  have hneg : (∑ Q : G, f (-Q)) = ∑ Q : G, f Q := Equiv.sum_comp (Equiv.neg G) f
  have hpairs (Q : G) : f Q + f (-Q) = 2 * r Q := by
    by_cases hQ : Q = 0
    · subst Q
      simp [f, r, xCoord]
      ring
    · have hQval : Q.val ≠ 0 := fun h => hQ (Subtype.ext h)
      rcases hval : Q.val with _ | ⟨u, v, hu⟩
      · exact (hQval hval).elim
      · have hmem : Affine.Point.some u v hu ∈ G := hval ▸ Q.property
        have hxu := xCoord_ne_of_not_mem E G hP hPG hu hmem
        have h := xCoord_add_pair E hP hu hxu
        dsimp [f, r]
        rw [ite_eq_right hQ]
        simp only [hval, Affine.Point.neg_some, xCoord]
        change _ = _
        rw [show Affine.Point.some x y hP +
            Affine.Point.some u (E.toAffine.negY u v) _ =
            Affine.Point.some x y hP - Affine.Point.some u v hu by
          rw [sub_eq_add_neg, Affine.Point.neg_some]]
        dsimp [tTerm]
        dsimp [xCoord] at h
        field_simp at h ⊢
        linear_combination h
  change (∑ Q : G, f Q) = ∑ Q : G, r Q
  apply mul_left_cancel₀ (NeZero.ne (2 : K))
  calc
    2 * ∑ Q : G, f Q = (∑ Q : G, f Q) + ∑ Q : G, f (-Q) := by rw [hneg]; ring
    _ = ∑ Q : G, (f Q + f (-Q)) := Finset.sum_add_distrib.symm
    _ = ∑ Q : G, 2 * r Q := Finset.sum_congr rfl (fun Q _ => hpairs Q)
    _ = 2 * ∑ Q : G, r Q := (Finset.mul_sum ..).symm



/-- Paired translates give the rational y-coordinate correction. -/
theorem yCoord_add_pair (E : WeierstrassCurve K) {x y u v : K}
    (hP : E.toAffine.Nonsingular x y) (hQ : E.toAffine.Nonsingular u v)
    (hxu : x ≠ u) :
    2 * (yCoord (Affine.Point.some x y hP + Affine.Point.some u v hQ) +
      yCoord (Affine.Point.some x y hP - Affine.Point.some u v hQ) + E.a₁ * u + E.a₃) =
      -(2 * y + E.a₁ * x + E.a₃) *
        ((6 * u ^ 2 + E.b₂ * u + E.b₄) / (x - u) ^ 2 +
          2 * (4 * u ^ 3 + E.b₂ * u ^ 2 + 2 * E.b₄ * u + E.b₆) / (x - u) ^ 3) -
        E.a₁ * ((6 * u ^ 2 + E.b₂ * u + E.b₄) / (x - u) +
          (4 * u ^ 3 + E.b₂ * u ^ 2 + 2 * E.b₄ * u + E.b₆) / (x - u) ^ 2) := by
  simp only [sub_eq_add_neg (Affine.Point.some x y hP), Affine.Point.neg_some,
    Affine.Point.add_of_X_ne hxu, yCoord, Affine.slope_of_X_ne hxu]
  have hp := (Affine.equation_iff _ _).mp hP.1
  have hq := (Affine.equation_iff _ _).mp hQ.1
  dsimp [Affine.addY, Affine.negAddY, Affine.addX, Affine.negY, b₂, b₄, b₆]
  field_simp
  linear_combination
    2 * (E.a₁ * u - 2 * E.a₁ * x - E.a₃ - 2 * y) * hp +
    2 * (E.a₁ * u - 4 * E.a₁ * x - 3 * E.a₃ - 6 * y) * hq



/-- The y-map is rational in the original affine coordinates. -/
theorem yMap_eq_sum_rational [NeZero (2 : K)] (E : WeierstrassCurve K)
    (G : AddSubgroup E.toAffine.Point) [Fintype G] {x y : K}
    (hP : E.toAffine.Nonsingular x y) (hPG : Affine.Point.some x y hP ∉ G) :
    yMap E G (.some x y hP) =
      ∑ Q : G, if Q = 0 then y else
        (-(2 * y + E.a₁ * x + E.a₃) *
          ((6 * xCoord Q.val ^ 2 + E.b₂ * xCoord Q.val + E.b₄) /
              (x - xCoord Q.val) ^ 2 +
            2 * (4 * xCoord Q.val ^ 3 + E.b₂ * xCoord Q.val ^ 2 +
              2 * E.b₄ * xCoord Q.val + E.b₆) / (x - xCoord Q.val) ^ 3) -
          E.a₁ * ((6 * xCoord Q.val ^ 2 + E.b₂ * xCoord Q.val + E.b₄) /
              (x - xCoord Q.val) +
            (4 * xCoord Q.val ^ 3 + E.b₂ * xCoord Q.val ^ 2 +
              2 * E.b₄ * xCoord Q.val + E.b₆) / (x - xCoord Q.val) ^ 2)) / 4 := by
  classical
  let f (Q : G) := yCoord (Affine.Point.some x y hP + Q.val) - yCoord Q.val
  let r (Q : G) := if Q = 0 then y else
    (-(2 * y + E.a₁ * x + E.a₃) *
      ((6 * xCoord Q.val ^ 2 + E.b₂ * xCoord Q.val + E.b₄) /
          (x - xCoord Q.val) ^ 2 +
        2 * (4 * xCoord Q.val ^ 3 + E.b₂ * xCoord Q.val ^ 2 +
          2 * E.b₄ * xCoord Q.val + E.b₆) / (x - xCoord Q.val) ^ 3) -
      E.a₁ * ((6 * xCoord Q.val ^ 2 + E.b₂ * xCoord Q.val + E.b₄) /
          (x - xCoord Q.val) +
        (4 * xCoord Q.val ^ 3 + E.b₂ * xCoord Q.val ^ 2 +
          2 * E.b₄ * xCoord Q.val + E.b₆) / (x - xCoord Q.val) ^ 2)) / 4
  have hneg : (∑ Q : G, f (-Q)) = ∑ Q : G, f Q := Equiv.sum_comp (Equiv.neg G) f
  have hpairs (Q : G) : f Q + f (-Q) = 2 * r Q := by
    by_cases hQ : Q = 0
    · subst Q
      simp [f, r, yCoord]
      ring
    · have hQval : Q.val ≠ 0 := fun h => hQ (Subtype.ext h)
      rcases hval : Q.val with _ | ⟨u, v, hu⟩
      · exact (hQval hval).elim
      · have hmem : Affine.Point.some u v hu ∈ G := hval ▸ Q.property
        have hxu := xCoord_ne_of_not_mem E G hP hPG hu hmem
        have h := yCoord_add_pair E hP hu hxu
        dsimp [f, r]
        rw [ite_eq_right hQ]
        simp only [hval, Affine.Point.neg_some, xCoord, yCoord]
        rw [show Affine.Point.some x y hP +
            Affine.Point.some u (E.toAffine.negY u v) _ =
            Affine.Point.some x y hP - Affine.Point.some u v hu by
          rw [sub_eq_add_neg, Affine.Point.neg_some]]
        dsimp [Affine.negY]
        dsimp [yCoord] at h
        have h4 : (4 : K) ≠ 0 := by
          have := mul_ne_zero (NeZero.ne (2 : K)) (NeZero.ne (2 : K))
          norm_num at this ⊢
          exact this
        field_simp at h ⊢
        linear_combination 2 * h
  change (∑ Q : G, f Q) = ∑ Q : G, r Q
  apply mul_left_cancel₀ (NeZero.ne (2 : K))
  calc
    2 * ∑ Q : G, f Q = (∑ Q : G, f Q) + ∑ Q : G, f (-Q) := by rw [hneg]; ring
    _ = ∑ Q : G, (f Q + f (-Q)) := Finset.sum_add_distrib.symm
    _ = ∑ Q : G, 2 * r Q := Finset.sum_congr rfl (fun Q _ => hpairs Q)
    _ = 2 * ∑ Q : G, r Q := (Finset.mul_sum ..).symm


end WeierstrassCurve.Velu
