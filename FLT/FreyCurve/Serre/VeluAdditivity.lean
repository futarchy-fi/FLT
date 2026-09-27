/-
Copyright (c) 2026 krandder. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: krandder
-/
module

public import FLT.FreyCurve.Serre.VeluGenericAdditivity

/-!
# Exceptional cases for additivity of Vélu's map

The coordinate map preserves negation. Kernel-coset invariance then proves the
addition law whenever either summand or their sum lies in the kernel. The full
addition theorem is reduced to the case where all three points lie outside
the kernel; that remaining addition identity is not proved here.
-/

@[expose] public section

open scoped BigOperators WeierstrassCurve.Affine
namespace WeierstrassCurve.Velu
variable {K : Type*} [Field K] [DecidableEq K]
variable (E : WeierstrassCurve K) (G : AddSubgroup E.toAffine.Point) [Fintype G]

/-- The Vélu x-coordinate is unchanged by negation. -/
theorem xMap_neg (P : E.toAffine.Point) : xMap E G (-P) = xMap E G P := by
  change (∑ Q : G, (xCoord (-P + Q.val) - xCoord Q.val)) = _
  rw [← Equiv.sum_comp (Equiv.neg G) (fun Q : G =>
    xCoord (-P + Q.val) - xCoord Q.val)]
  apply Finset.sum_congr rfl
  intro Q _
  simp only [Equiv.neg_apply, AddSubgroup.coe_neg, ← neg_add, xCoord_neg]

/-- Away from the kernel, negation has the target Weierstrass y-coordinate formula. -/
theorem yMap_neg_of_not_mem [NeZero (2 : K)] (P : E.toAffine.Point) (hP : P ∉ G) :
    yMap E G (-P) = -yMap E G P - E.a₁ * xMap E G P - E.a₃ := by
  have hn : -P ∉ G := by simpa using hP
  cases P with
  | zero => exact (hP G.zero_mem).elim
  | some x y hp =>
    have hpos := completed_yMap E G hp hP
    have hneg := completed_yMap E G ((Affine.nonsingular_neg ..).mpr hp) hn
    have hx := xMap_neg E G (.some x y hp)
    simp only [Affine.Point.neg_some] at hx ⊢
    rw [hx] at hneg
    dsimp [Affine.negY] at hneg ⊢
    apply mul_left_cancel₀ (NeZero.ne (2 : K))
    linear_combination hpos + hneg

/-- The point map preserves negation when the target has the prescribed a₁ and a₃. -/
theorem pointMap_neg [NeZero (2 : K)] (E' : WeierstrassCurve K)
    (h : ∀ P, P ∉ G → E'.toAffine.Nonsingular (xMap E G P) (yMap E G P))
    (ha₁ : E'.a₁ = E.a₁) (ha₃ : E'.a₃ = E.a₃) (P : E.toAffine.Point) :
    pointMap E G E' h (-P) = -pointMap E G E' h P := by
  by_cases hP : P ∈ G
  · simp [pointMap, hP, G.neg_mem hP]
  · have hn : -P ∉ G := by simpa using hP
    simp only [pointMap, dite_eq_right hP, dite_eq_right hn, Affine.Point.neg_some,
      xMap_neg, yMap_neg_of_not_mem E G P hP, Affine.negY, ha₁, ha₃]


/-- The addition law holds when the second summand lies in the kernel. -/
theorem pointMap_add_of_mem_right (E' : WeierstrassCurve K)
    (h : ∀ P, P ∉ G → E'.toAffine.Nonsingular (xMap E G P) (yMap E G P))
    (P Q : E.toAffine.Point) (hQ : Q ∈ G) :
    pointMap E G E' h (P + Q) = pointMap E G E' h P + pointMap E G E' h Q := by
  rw [(pointMap_eq_zero_iff E G E' h Q).mpr hQ, add_zero]
  exact pointMap_add_kernel E G E' h P ⟨Q, hQ⟩

/-- The addition law holds when the sum lies in the kernel. -/
theorem pointMap_add_of_sum_mem [NeZero (2 : K)] (E' : WeierstrassCurve K)
    (h : ∀ P, P ∉ G → E'.toAffine.Nonsingular (xMap E G P) (yMap E G P))
    (ha₁ : E'.a₁ = E.a₁) (ha₃ : E'.a₃ = E.a₃)
    (P Q : E.toAffine.Point) (hPQ : P + Q ∈ G) :
    pointMap E G E' h (P + Q) = pointMap E G E' h P + pointMap E G E' h Q := by
  rw [(pointMap_eq_zero_iff E G E' h (P + Q)).mpr hPQ]
  have hh := pointMap_add_kernel E G E' h (-P) ⟨P + Q, hPQ⟩
  simp only [neg_add_cancel_left, pointMap_neg E G E' h ha₁ ha₃] at hh
  rw [hh, add_neg_cancel]

/-- It suffices to prove additivity when both summands and their sum avoid the kernel. -/
theorem pointMap_add_of_add_off_kernel [NeZero (2 : K)] (E' : WeierstrassCurve K)
    (h : ∀ P, P ∉ G → E'.toAffine.Nonsingular (xMap E G P) (yMap E G P))
    (ha₁ : E'.a₁ = E.a₁) (ha₃ : E'.a₃ = E.a₃)
    (hadd : ∀ P Q, P ∉ G → Q ∉ G → P + Q ∉ G →
      pointMap E G E' h (P + Q) = pointMap E G E' h P + pointMap E G E' h Q)
    (P Q : E.toAffine.Point) :
    pointMap E G E' h (P + Q) = pointMap E G E' h P + pointMap E G E' h Q := by
  by_cases hP : P ∈ G
  · simpa only [add_comm] using pointMap_add_of_mem_right E G E' h Q P hP
  by_cases hQ : Q ∈ G
  · exact pointMap_add_of_mem_right E G E' h P Q hQ
  by_cases hPQ : P + Q ∈ G
  · exact pointMap_add_of_sum_mem E G E' h ha₁ ha₃ P Q hPQ
  exact hadd P Q hP hQ hPQ

end WeierstrassCurve.Velu
