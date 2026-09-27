/-
Copyright (c) 2026 krandder. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: krandder
-/
module

public import FLT.FreyCurve.Serre.VeluCoordinates

/-!
# Reducing the candidate Vélu equation

The completed y-coordinate reduces the candidate curve equation to an identity
of rational expressions in x. Translation sums and duplication give the regular
x and slope sums at kernel points distinct from their inverses.

These are intermediate identities. The rational identity, nonsingularity of the
candidate curve, and additivity of its point map remain separate obligations.
-/

@[expose] public section

open scoped BigOperators WeierstrassCurve.Affine
namespace WeierstrassCurve.Velu
variable {K : Type*} [Field K] [DecidableEq K]

/-- The correction factor of the invariant differential in Vélu's formula. -/
noncomputable def slopeFactor (E : WeierstrassCurve K)
    (G : AddSubgroup E.toAffine.Point) [Fintype G] (x : K) : K := by
  classical
  exact ∑ Q : G, if Q = 0 then 1 else
    -tTerm E (xCoord Q.val) / (x - xCoord Q.val) ^ 2 -
      (4 * xCoord Q.val ^ 3 + E.b₂ * xCoord Q.val ^ 2 +
        2 * E.b₄ * xCoord Q.val + E.b₆) / (x - xCoord Q.val) ^ 3

/-- The completed y-coordinate is the source completed coordinate times the slope factor. -/
theorem completed_yMap [NeZero (2 : K)] (E : WeierstrassCurve K)
    (G : AddSubgroup E.toAffine.Point) [Fintype G] {x y : K}
    (hP : E.toAffine.Nonsingular x y) (hPG : Affine.Point.some x y hP ∉ G) :
    2 * yMap E G (.some x y hP) + E.a₁ * xMap E G (.some x y hP) + E.a₃ =
      (2 * y + E.a₁ * x + E.a₃) * slopeFactor E G x := by
  classical
  rw [xMap_eq_sum_rational E G hP hPG, yMap_eq_sum_rational E G hP hPG]
  simp only [Finset.mul_sum, ← Finset.sum_add_distrib]
  have h4 : (4 : K) ≠ 0 := by
    have := mul_ne_zero (NeZero.ne (2 : K)) (NeZero.ne (2 : K))
    norm_num at this ⊢
    exact this
  have hterm (Q : G) :
      2 * (if Q = 0 then y else
        (-(2 * y + E.a₁ * x + E.a₃) *
          ((6 * xCoord Q.val ^ 2 + E.b₂ * xCoord Q.val + E.b₄) /
              (x - xCoord Q.val) ^ 2 +
            2 * (4 * xCoord Q.val ^ 3 + E.b₂ * xCoord Q.val ^ 2 +
              2 * E.b₄ * xCoord Q.val + E.b₆) / (x - xCoord Q.val) ^ 3) -
          E.a₁ * ((6 * xCoord Q.val ^ 2 + E.b₂ * xCoord Q.val + E.b₄) /
              (x - xCoord Q.val) +
            (4 * xCoord Q.val ^ 3 + E.b₂ * xCoord Q.val ^ 2 +
              2 * E.b₄ * xCoord Q.val + E.b₆) / (x - xCoord Q.val) ^ 2)) / 4) +
      E.a₁ * (if Q = 0 then x else
        tTerm E (xCoord Q.val) / (x - xCoord Q.val) +
          (4 * xCoord Q.val ^ 3 + E.b₂ * xCoord Q.val ^ 2 +
            2 * E.b₄ * xCoord Q.val + E.b₆) / (2 * (x - xCoord Q.val) ^ 2)) =
      (2 * y + E.a₁ * x + E.a₃) *
        (if Q = 0 then 1 else
          -tTerm E (xCoord Q.val) / (x - xCoord Q.val) ^ 2 -
            (4 * xCoord Q.val ^ 3 + E.b₂ * xCoord Q.val ^ 2 +
              2 * E.b₄ * xCoord Q.val + E.b₆) / (x - xCoord Q.val) ^ 3) -
        (if Q = 0 then E.a₃ else 0) := by
    by_cases hQ : Q = 0
    · simp only [hQ, ite_true]; ring
    · simp only [hQ, ite_false]
      by_cases hx : x - xCoord Q.val = 0
      · simp [hx]
      · dsimp [tTerm]
        field_simp
        ring
  simp_rw [hterm, Finset.sum_sub_distrib, ← Finset.mul_sum]
  simp [slopeFactor]

/-- Landing on the candidate curve is equivalent to one rational identity in x.
This is a reduction of the geometric obligation, not a proof that it always holds. -/
theorem equation_iff_univariate_identity [NeZero (2 : K)] (E : WeierstrassCurve K)
    (G : AddSubgroup E.toAffine.Point) [Fintype G] {x y : K}
    (hP : E.toAffine.Nonsingular x y) (hPG : Affine.Point.some x y hP ∉ G) :
    (curve E G).toAffine.Equation
      (xMap E G (.some x y hP)) (yMap E G (.some x y hP)) ↔
    (4 * x ^ 3 + E.b₂ * x ^ 2 + 2 * E.b₄ * x + E.b₆) * slopeFactor E G x ^ 2 =
      4 * xMap E G (.some x y hP) ^ 3 +
        E.b₂ * xMap E G (.some x y hP) ^ 2 +
        (2 * E.b₄ - 20 * t E G) * xMap E G (.some x y hP) +
        E.b₆ - 4 * E.b₂ * t E G - 28 * w E G := by
  let X := xMap E G (.some x y hP)
  let Y := yMap E G (.some x y hP)
  let D := slopeFactor E G x
  let T := t E G
  let W := w E G
  have hs : 2 * Y + E.a₁ * X + E.a₃ = (2 * y + E.a₁ * x + E.a₃) * D :=
    completed_yMap E G hP hPG
  have hp := (Affine.equation_iff _ _).mp hP.1
  rw [Affine.equation_iff]
  change (Y ^ 2 + E.a₁ * X * Y + E.a₃ * Y =
    X ^ 3 + E.a₂ * X ^ 2 + (E.a₄ - 5 * T) * X +
      (E.a₆ - E.b₂ * T - 7 * W)) ↔
    (4 * x ^ 3 + E.b₂ * x ^ 2 + 2 * E.b₄ * x + E.b₆) * D ^ 2 =
      4 * X ^ 3 + E.b₂ * X ^ 2 + (2 * E.b₄ - 20 * T) * X +
        E.b₆ - 4 * E.b₂ * T - 28 * W
  dsimp only [b₂, b₄, b₆]
  constructor
  · intro ht
    linear_combination
      4 * ht - (2 * Y + E.a₁ * X + E.a₃ + (2 * y + E.a₁ * x + E.a₃) * D) * hs -
        4 * D ^ 2 * hp
  · intro hr
    have h4 : (4 : K) ≠ 0 := by
      have := mul_ne_zero (NeZero.ne (2 : K)) (NeZero.ne (2 : K))
      norm_num at this ⊢
      exact this
    apply mul_left_cancel₀ h4
    linear_combination
      hr + (2 * Y + E.a₁ * X + E.a₃ + (2 * y + E.a₁ * x + E.a₃) * D) * hs +
        4 * D ^ 2 * hp

/-- Removing the identity and an inverse pair isolates the doubling term in a translation sum. -/
theorem sumCoord_erase_pair {A B : Type*} [AddCommGroup A] [DecidableEq A] [AddCommGroup B]
    (G : AddSubgroup A) [Fintype G] (f : A → B) (hf : f 0 = 0)
    (Q : G) (hQ : Q ≠ 0) (hQneg : Q ≠ -Q) :
    ∑ R ∈ ((Finset.univ.erase (0 : G)).erase Q).erase (-Q),
      (f (Q.val + R.val) - f R.val) = f (-Q.val) - f (Q.val + Q.val) := by
  classical
  let d (R : G) := f (Q.val + R.val) - f R.val
  have hs : ∑ R : G, d R = 0 := sumCoord_of_mem G f Q.property
  have h0 := Finset.sum_erase_add (Finset.univ : Finset G) d (Finset.mem_univ (0 : G))
  have h1 := Finset.sum_erase_add (Finset.univ.erase (0 : G)) d
    (show Q ∈ Finset.univ.erase (0 : G) by simp [hQ])
  have h2 := Finset.sum_erase_add ((Finset.univ.erase (0 : G)).erase Q) d
    (show -Q ∈ (Finset.univ.erase (0 : G)).erase Q by
      simp [hQ, Ne.symm hQneg])
  have hd0 : d 0 = f Q.val := by simp [d, hf]
  have hdQ : d Q = f (Q.val + Q.val) - f Q.val := rfl
  have hdneg : d (-Q) = -f (-Q.val) := by simp [d, hf]
  change ∑ R ∈ ((Finset.univ.erase (0 : G)).erase Q).erase (-Q), d R = _
  apply sub_eq_zero.mp
  calc
    _ = ((∑ R ∈ ((Finset.univ.erase (0 : G)).erase Q).erase (-Q), d R) +
      d (-Q)) + d Q + d 0 := by rw [hd0, hdQ, hdneg]; abel
    _ = 0 := by rw [h2, h1, h0, hs]

/-- The regular part of the rational x-sum at a non-two-torsion kernel point is
determined by doubling that point. This supplies a local cancellation identity. -/
theorem regular_xSum_at_kernel [NeZero (2 : K)] (E : WeierstrassCurve K)
    (G : AddSubgroup E.toAffine.Point) [Fintype G] (Q : G)
    {u v : K} (hu : E.toAffine.Nonsingular u v)
    (hval : Q.val = Affine.Point.some u v hu) (hQneg : Q ≠ -Q) :
    u + ∑ R ∈ ((Finset.univ.erase (0 : G)).erase Q).erase (-Q),
      (tTerm E (xCoord R.val) / (u - xCoord R.val) +
        (4 * xCoord R.val ^ 3 + E.b₂ * xCoord R.val ^ 2 +
          2 * E.b₄ * xCoord R.val + E.b₆) / (2 * (u - xCoord R.val) ^ 2)) =
      2 * u - xCoord (Q.val + Q.val) := by
  classical
  let S := ((Finset.univ.erase (0 : G)).erase Q).erase (-Q)
  let f (R : G) := xCoord (Q.val + R.val) - xCoord R.val
  let r (R : G) := tTerm E (xCoord R.val) / (u - xCoord R.val) +
    (4 * xCoord R.val ^ 3 + E.b₂ * xCoord R.val ^ 2 +
      2 * E.b₄ * xCoord R.val + E.b₆) / (2 * (u - xCoord R.val) ^ 2)
  have hQ : Q ≠ 0 := by
    intro h
    have hz : Q.val = 0 := congrArg Subtype.val h
    rw [hval] at hz
    exact Affine.Point.some_ne_zero hu hz
  have hs : ∑ R ∈ S, f R = u - xCoord (Q.val + Q.val) := by
    have h := sumCoord_erase_pair G (@xCoord K _ E) rfl Q hQ hQneg
    simpa only [S, f, hval, Affine.Point.neg_some, xCoord] using h
  have hneg : (∑ R ∈ S, f (-R)) = ∑ R ∈ S, f R := by
    apply Finset.sum_equiv (Equiv.neg G)
    · intro R
      simp [S, neg_eq_iff_eq_neg, and_comm, and_left_comm]
    · intro R _
      rfl
  have hpairs (R : G) (hR : R ∈ S) : f R + f (-R) = 2 * r R := by
    have hm : R ≠ -Q ∧ R ≠ Q ∧ R ≠ 0 := by simpa [S] using hR
    have hR0 : R.val ≠ 0 := fun h => hm.2.2 (Subtype.ext h)
    rcases hrv : R.val with _ | ⟨a, b, ha⟩
    · exact (hR0 hrv).elim
    · have hua : u ≠ a := by
        intro h
        have hx : Q.val.xRep = R.val.xRep := by
          rw [hval, hrv]
          simp only [Affine.Point.xRep_some, h]
        rcases Affine.Point.eq_or_eq_neg_of_xRep_eq_xRep hx with heq | heq
        · exact hm.2.1 (Subtype.ext heq.symm)
        · apply hm.1
          apply Subtype.ext
          change R.val = -Q.val
          rw [heq, neg_neg]
      have hp := xCoord_add_pair E hu ha hua
      dsimp [f, r]
      simp only [hval, hrv, Affine.Point.neg_some, xCoord]
      rw [show Affine.Point.some u v hu + Affine.Point.some a (E.toAffine.negY a b) _ =
          Affine.Point.some u v hu - Affine.Point.some a b ha by
        rw [sub_eq_add_neg, Affine.Point.neg_some]]
      dsimp [tTerm]
      dsimp [xCoord] at hp
      field_simp at hp ⊢
      linear_combination hp
  have hsum : (∑ R ∈ S, f R) = ∑ R ∈ S, r R := by
    apply mul_left_cancel₀ (NeZero.ne (2 : K))
    calc
      2 * ∑ R ∈ S, f R = (∑ R ∈ S, f R) + ∑ R ∈ S, f (-R) := by rw [hneg]; ring
      _ = ∑ R ∈ S, (f R + f (-R)) := Finset.sum_add_distrib.symm
      _ = ∑ R ∈ S, 2 * r R := Finset.sum_congr rfl hpairs
      _ = 2 * ∑ R ∈ S, r R := (Finset.mul_sum ..).symm
  change u + ∑ R ∈ S, r R = _
  rw [← hsum, hs]
  ring

/-- The duplication formula in the form needed for pole cancellation. -/
theorem duplication_pole_identity (E : WeierstrassCurve K) {u v : K}
    (hu : E.toAffine.Nonsingular u v) (hv : v ≠ E.toAffine.negY u v) :
    (4 * u ^ 3 + E.b₂ * u ^ 2 + 2 * E.b₄ * u + E.b₆) *
      (4 * xCoord (Affine.Point.some u v hu + Affine.Point.some u v hu) +
        8 * u + E.b₂) =
      (6 * u ^ 2 + E.b₂ * u + E.b₄) ^ 2 := by
  have hd : 4 * u ^ 3 + E.b₂ * u ^ 2 + 2 * E.b₄ * u + E.b₆ ≠ 0 :=
    (Affine.den_duplication_eq_zero_iff hu.1).not.mpr hv
  simp only [Affine.Point.add_self_of_Y_ne hv, xCoord,
    Affine.addX_self_of_Y_ne hu.1 hv]
  change _ * (4 * ((u ^ 4 - E.b₄ * u ^ 2 - 2 * E.b₆ * u - E.b₈) /
    (4 * u ^ 3 + E.b₂ * u ^ 2 + 2 * E.b₄ * u + E.b₆)) + 8 * u + E.b₂) = _
  have hc := div_mul_cancel₀ (u ^ 4 - E.b₄ * u ^ 2 - 2 * E.b₆ * u - E.b₈) hd
  dsimp [b₂, b₄, b₆, b₈] at hc ⊢
  linear_combination 4 * hc

/-- The regular x-sum cancels the fourth-order coefficient in the candidate equation. -/
theorem regular_xSum_pole_cancellation [NeZero (2 : K)] (E : WeierstrassCurve K)
    (G : AddSubgroup E.toAffine.Point) [Fintype G] (Q : G)
    {u v : K} (hu : E.toAffine.Nonsingular u v)
    (hval : Q.val = Affine.Point.some u v hu) (hQneg : Q ≠ -Q) :
    (4 * u ^ 3 + E.b₂ * u ^ 2 + 2 * E.b₄ * u + E.b₆) *
      (48 * u + 3 * E.b₂ - 12 *
        (u + ∑ R ∈ ((Finset.univ.erase (0 : G)).erase Q).erase (-Q),
          (tTerm E (xCoord R.val) / (u - xCoord R.val) +
            (4 * xCoord R.val ^ 3 + E.b₂ * xCoord R.val ^ 2 +
              2 * E.b₄ * xCoord R.val + E.b₆) / (2 * (u - xCoord R.val) ^ 2)))) =
      3 * (6 * u ^ 2 + E.b₂ * u + E.b₄) ^ 2 := by
  have hv : v ≠ E.toAffine.negY u v := by
    intro h
    apply hQneg
    apply Subtype.ext
    change Q.val = -Q.val
    rw [hval, Affine.Point.neg_some]
    congr 1
  rw [regular_xSum_at_kernel E G Q hu hval hQneg, hval]
  linear_combination 3 * duplication_pole_identity E hu hv

/-- The regular slope sum at a kernel point is controlled by the completed
y-coordinate of its double. -/
theorem regular_slopeSum_at_kernel [NeZero (2 : K)] (E : WeierstrassCurve K)
    (G : AddSubgroup E.toAffine.Point) [Fintype G] (Q : G)
    {u v : K} (hu : E.toAffine.Nonsingular u v)
    (hval : Q.val = Affine.Point.some u v hu) (hQneg : Q ≠ -Q) :
    (2 * v + E.a₁ * u + E.a₃) *
      (1 + ∑ R ∈ ((Finset.univ.erase (0 : G)).erase Q).erase (-Q),
        (-tTerm E (xCoord R.val) / (u - xCoord R.val) ^ 2 -
          (4 * xCoord R.val ^ 3 + E.b₂ * xCoord R.val ^ 2 +
            2 * E.b₄ * xCoord R.val + E.b₆) / (u - xCoord R.val) ^ 3)) =
      -(2 * yCoord (Q.val + Q.val) + E.a₁ * xCoord (Q.val + Q.val) + E.a₃) := by
  classical
  let S := ((Finset.univ.erase (0 : G)).erase Q).erase (-Q)
  let z (P : E.toAffine.Point) := 2 * yCoord P + E.a₁ * xCoord P
  let f (R : G) := z (Q.val + R.val) - z R.val
  let r (R : G) := -tTerm E (xCoord R.val) / (u - xCoord R.val) ^ 2 -
    (4 * xCoord R.val ^ 3 + E.b₂ * xCoord R.val ^ 2 +
      2 * E.b₄ * xCoord R.val + E.b₆) / (u - xCoord R.val) ^ 3
  let Z := 2 * v + E.a₁ * u + E.a₃
  have hQ : Q ≠ 0 := by
    intro h
    have hz : Q.val = 0 := congrArg Subtype.val h
    rw [hval] at hz
    exact Affine.Point.some_ne_zero hu hz
  have hs : ∑ R ∈ S, f R = -Z - E.a₃ - z (Q.val + Q.val) := by
    have h := sumCoord_erase_pair G z (by simp [z, xCoord, yCoord]) Q hQ hQneg
    change (∑ R ∈ S, f R) = _ at h
    rw [h]
    simp only [z, hval, Affine.Point.neg_some, xCoord, yCoord]
    dsimp [Affine.negY, Z]
    ring
  have hneg : (∑ R ∈ S, f (-R)) = ∑ R ∈ S, f R := by
    apply Finset.sum_equiv (Equiv.neg G)
    · intro R
      simp [S, neg_eq_iff_eq_neg, and_comm, and_left_comm]
    · intro R _
      rfl
  have hpairs (R : G) (hR : R ∈ S) : f R + f (-R) = 2 * (Z * r R) := by
    have hm : R ≠ -Q ∧ R ≠ Q ∧ R ≠ 0 := by simpa [S] using hR
    have hR0 : R.val ≠ 0 := fun h => hm.2.2 (Subtype.ext h)
    rcases hrv : R.val with _ | ⟨a, b, ha⟩
    · exact (hR0 hrv).elim
    · have hua : u ≠ a := by
        intro h
        have hx : Q.val.xRep = R.val.xRep := by
          rw [hval, hrv]
          simp only [Affine.Point.xRep_some, h]
        rcases Affine.Point.eq_or_eq_neg_of_xRep_eq_xRep hx with heq | heq
        · exact hm.2.1 (Subtype.ext heq.symm)
        · apply hm.1
          apply Subtype.ext
          change R.val = -Q.val
          rw [heq, neg_neg]
      have hx := xCoord_add_pair E hu ha hua
      have hy := yCoord_add_pair E hu ha hua
      dsimp [f, z, r, Z]
      simp only [hval, hrv, Affine.Point.neg_some, xCoord, yCoord]
      rw [show Affine.Point.some u v hu + Affine.Point.some a (E.toAffine.negY a b) _ =
          Affine.Point.some u v hu - Affine.Point.some a b ha by
        rw [sub_eq_add_neg, Affine.Point.neg_some]]
      dsimp [tTerm, Affine.negY]
      dsimp [xCoord] at hx
      dsimp [yCoord] at hy
      field_simp at hx hy ⊢
      linear_combination E.a₁ * (u - a) * hx + hy
  have hsum : (∑ R ∈ S, f R) = Z * ∑ R ∈ S, r R := by
    apply mul_left_cancel₀ (NeZero.ne (2 : K))
    calc
      2 * ∑ R ∈ S, f R = (∑ R ∈ S, f R) + ∑ R ∈ S, f (-R) := by rw [hneg]; ring
      _ = ∑ R ∈ S, (f R + f (-R)) := Finset.sum_add_distrib.symm
      _ = ∑ R ∈ S, 2 * (Z * r R) := Finset.sum_congr rfl hpairs
      _ = 2 * (Z * ∑ R ∈ S, r R) := by rw [Finset.mul_sum, Finset.mul_sum]
  change Z * (1 + ∑ R ∈ S, r R) = -(z (Q.val + Q.val) + E.a₃)
  rw [mul_add, mul_one, ← hsum, hs]
  ring

/-- Completed y-coordinates under doubling, with denominators cleared. -/
theorem duplication_completed_y (E : WeierstrassCurve K) {u v : K}
    (hu : E.toAffine.Nonsingular u v) (hv : v ≠ E.toAffine.negY u v) :
    (2 * v + E.a₁ * u + E.a₃) *
      (2 * yCoord (Affine.Point.some u v hu + Affine.Point.some u v hu) +
        E.a₁ * xCoord (Affine.Point.some u v hu + Affine.Point.some u v hu) + E.a₃) =
      (6 * u ^ 2 + E.b₂ * u + E.b₄) *
        (u - xCoord (Affine.Point.some u v hu + Affine.Point.some u v hu)) -
      (4 * u ^ 3 + E.b₂ * u ^ 2 + 2 * E.b₄ * u + E.b₆) := by
  have hs : (2 * E.toAffine.slope u u v v + E.a₁) * (2 * v + E.a₁ * u + E.a₃) =
      6 * u ^ 2 + E.b₂ * u + E.b₄ := by
    rw [Affine.slope_of_Y_ne rfl hv]
    have hc := div_mul_cancel₀
      (3 * u ^ 2 + 2 * E.toAffine.a₂ * u + E.toAffine.a₄ - E.toAffine.a₁ * v)
      (sub_ne_zero.mpr hv)
    dsimp [Affine.negY, b₂, b₄] at hc ⊢
    linear_combination 2 * hc
  have hp := (Affine.equation_iff _ _).mp hu.1
  simp only [Affine.Point.add_self_of_Y_ne hv, xCoord, yCoord]
  dsimp only [Affine.addY, Affine.negAddY, Affine.negY]
  dsimp [b₂, b₄, b₆] at hs ⊢
  linear_combination (norm := (simp only [Affine.addX]; ring))
    -(E.toAffine.addX u u (E.toAffine.slope u u v v) - u) * hs - 4 * hp

/-- A rational x-only expression for the regular slope sum at a kernel point. -/
theorem regular_slopeSum_x_identity [NeZero (2 : K)] (E : WeierstrassCurve K)
    (G : AddSubgroup E.toAffine.Point) [Fintype G] (Q : G)
    {u v : K} (hu : E.toAffine.Nonsingular u v)
    (hval : Q.val = Affine.Point.some u v hu) (hQneg : Q ≠ -Q) :
    (4 * u ^ 3 + E.b₂ * u ^ 2 + 2 * E.b₄ * u + E.b₆) *
      (1 + ∑ R ∈ ((Finset.univ.erase (0 : G)).erase Q).erase (-Q),
        (-tTerm E (xCoord R.val) / (u - xCoord R.val) ^ 2 -
          (4 * xCoord R.val ^ 3 + E.b₂ * xCoord R.val ^ 2 +
            2 * E.b₄ * xCoord R.val + E.b₆) / (u - xCoord R.val) ^ 3)) =
      (4 * u ^ 3 + E.b₂ * u ^ 2 + 2 * E.b₄ * u + E.b₆) +
        (6 * u ^ 2 + E.b₂ * u + E.b₄) * (xCoord (Q.val + Q.val) - u) := by
  have hv : v ≠ E.toAffine.negY u v := by
    intro h
    apply hQneg
    apply Subtype.ext
    change Q.val = -Q.val
    rw [hval, Affine.Point.neg_some]
    congr 1
  have hs := regular_slopeSum_at_kernel E G Q hu hval hQneg
  have hd := duplication_completed_y E hu hv
  rw [← hval] at hd
  have hf : 4 * u ^ 3 + E.b₂ * u ^ 2 + 2 * E.b₄ * u + E.b₆ =
      (2 * v + E.a₁ * u + E.a₃) ^ 2 := Affine.den_duplication_eq hu.1
  rw [hf] at hd ⊢
  linear_combination (2 * v + E.a₁ * u + E.a₃) * hs - hd

/-- The regular x and slope sums cancel the third-order coefficient. -/
theorem regular_slopeSum_pole_cancellation [NeZero (2 : K)] (E : WeierstrassCurve K)
    (G : AddSubgroup E.toAffine.Point) [Fintype G] (Q : G)
    {u v : K} (hu : E.toAffine.Nonsingular u v)
    (hval : Q.val = Affine.Point.some u v hu) (hQneg : Q ≠ -Q) :
    let F := 4 * u ^ 3 + E.b₂ * u ^ 2 + 2 * E.b₄ * u + E.b₆
    let C := 6 * u ^ 2 + E.b₂ * u + E.b₄
    let R₀ := u + ∑ R ∈ ((Finset.univ.erase (0 : G)).erase Q).erase (-Q),
      (tTerm E (xCoord R.val) / (u - xCoord R.val) +
        (4 * xCoord R.val ^ 3 + E.b₂ * xCoord R.val ^ 2 +
          2 * E.b₄ * xCoord R.val + E.b₆) / (2 * (u - xCoord R.val) ^ 2))
    let R₁ := 1 + ∑ R ∈ ((Finset.univ.erase (0 : G)).erase Q).erase (-Q),
      (-tTerm E (xCoord R.val) / (u - xCoord R.val) ^ 2 -
        (4 * xCoord R.val ^ 3 + E.b₂ * xCoord R.val ^ 2 +
          2 * E.b₄ * xCoord R.val + E.b₆) / (u - xCoord R.val) ^ 3)
    8 * F ^ 2 * R₁ - 8 * F ^ 2 - F * E.b₂ * C +
      12 * F * C * R₀ - 24 * F * C * u + C ^ 3 = 0 := by
  have hv : v ≠ E.toAffine.negY u v := by
    intro h
    apply hQneg
    apply Subtype.ext
    change Q.val = -Q.val
    rw [hval, Affine.Point.neg_some]
    congr 1
  have hs := regular_slopeSum_x_identity E G Q hu hval hQneg
  have hd := duplication_pole_identity E hu hv
  rw [← hval] at hd
  dsimp only
  rw [regular_xSum_at_kernel E G Q hu hval hQneg]
  linear_combination
    8 * (4 * u ^ 3 + E.b₂ * u ^ 2 + 2 * E.b₄ * u + E.b₆) * hs -
      (6 * u ^ 2 + E.b₂ * u + E.b₄) * hd

end WeierstrassCurve.Velu
