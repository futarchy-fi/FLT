/-
Copyright (c) 2026 krandder. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: krandder
-/
module

public import FLT.EllipticCurve.CubicLegendreCyclicInvolutions

/-! # The local mixed Legendre relation

For compatible roots u of -1, v of 1-lambda and w of lambda, the root
u*v/w realizes the final reciprocal change. The swap-reciprocal-swap
and reciprocal-swap-reciprocal coordinate products agree exactly and
induce equal cyclic transports. Triple transport agrees with transport
by the product. Constructing a common coefficient cover carrying these
roots and descending the mixed relation remain separate obligations.
-/

@[expose] public noncomputable section
open AlgebraicGeometry CategoryTheory
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
namespace WeierstrassCurve.CubicCharts
universe u
variable {R : Type u} [CommRing R]

/-- The compatible root for the final reciprocal in the mixed relation. -/
def legendreBraidRoot (u v w : Rˣ) : Rˣ := u * v * w⁻¹

/-- The two mixed coordinate products agree for compatible roots. -/
theorem legendreCoordinate_braid (u v w : Rˣ)
    (hu : (u : R) ^ 2 = -1) (hv : (v : R) ^ 2 + (w : R) ^ 2 = 1) :
    legendreSwapChange u * legendreReciprocalChange v * legendreSwapChange u =
      legendreReciprocalChange (legendreBraidRoot u v w) *
        legendreSwapChange u * legendreReciprocalChange w := by
  ext <;> simp only [legendreSwapChange, legendreReciprocalChange,
    legendreBraidRoot, VariableChange.mul_def]
  · simp [mul_assoc, mul_left_comm, mul_comm]
  · simp only [one_mul, add_zero, hu]
    linear_combination -hv
  · simp
  · simp

/-- The compatible root squares to one minus the reciprocal parameter. -/
theorem legendreBraidRoot_square (l a u v w : Rˣ)
    (ha : (a : R) = 1 - l) (hu : (u : R) ^ 2 = -1)
    (hv : (v : R) ^ 2 = a) (hw : (w : R) ^ 2 = l) :
    (legendreBraidRoot u v w : R) ^ 2 = 1 - ((l⁻¹ : Rˣ) : R) := by
  have hi : ((w⁻¹ : Rˣ) : R) ^ 2 = (l⁻¹ : Rˣ) := by
    have h : w ^ 2 = l := Units.ext hw
    change ((w⁻¹ ^ 2 : Rˣ) : R) = ((l⁻¹ : Rˣ) : R)
    rw [inv_pow, h]
  simp only [legendreBraidRoot, Units.val_mul, mul_pow, hu, hv, hi, ha]
  have h : (l : R) * ((l⁻¹ : Rˣ) : R) = 1 := by simp
  linear_combination h

/-- The two mixed parameter transformations have the same endpoint. -/
theorem legendreBraidParameter (l a : Rˣ) (ha : (a : R) = 1 - l) :
    1 - ((a⁻¹ : Rˣ) : R) = ((((-a) * l⁻¹)⁻¹ : Rˣ) : R) := by
  simp only [mul_inv_rev, inv_inv, Units.val_mul]
  have h : (a : R) * ((a⁻¹ : Rˣ) : R) = 1 := by simp
  rw [ha] at h
  have hn : (-a)⁻¹ = -a⁻¹ := by
    apply inv_eq_of_mul_eq_one_left
    simp
  rw [hn, Units.val_neg]
  linear_combination -h

/-- The swap-reciprocal-swap product has the stated final Legendre equation. -/
theorem legendreBraidLeft_equation (l a u v : Rˣ)
    (ha : (a : R) = 1 - l) (hu : (u : R) ^ 2 = -1) (hv : (v : R) ^ 2 = a) :
    (legendreSwapChange u * legendreReciprocalChange v * legendreSwapChange u) •
      legendreCurve (l : R) = legendreCurve (1 - ((a⁻¹ : Rˣ) : R)) := by
  rw [mul_smul, legendreSwapChange_curve _ _ hu, ← ha, mul_smul,
    legendreReciprocalChange_curve a v hv, legendreSwapChange_curve _ _ hu]

/-- The reciprocal-swap-reciprocal product has the same final equation. -/
theorem legendreBraidRight_equation (l a u v w : Rˣ)
    (ha : (a : R) = 1 - l) (hu : (u : R) ^ 2 = -1)
    (hv : (v : R) ^ 2 = a) (hw : (w : R) ^ 2 = l) :
    (legendreReciprocalChange (legendreBraidRoot u v w) * legendreSwapChange u *
      legendreReciprocalChange w) • legendreCurve (l : R) =
        legendreCurve (1 - ((a⁻¹ : Rˣ) : R)) := by
  rw [← legendreCoordinate_braid u v w hu (by rw [hv, hw, ha]; ring)]
  exact legendreBraidLeft_equation l a u v ha hu hv

variable [IsNoetherianRing R] [IsDomain R]
variable (p : ℕ) [Fact p.Prime] [Fact (IsUnit (p : R))]
/-- The mixed coordinate products induce equal local cyclic transports. -/
theorem legendreBraid_cyclic (l a u v w : Rˣ)
    (ha : (a : R) = 1 - l) (hu : (u : R) ^ 2 = -1)
    (hv : (v : R) ^ 2 = a) (hw : (w : R) ^ 2 = l)
    [(legendreCurve (l : R)).IsElliptic]
    [(legendreCurve (1 - ((a⁻¹ : Rˣ) : R))).IsElliptic] :
    groupCyclicParameterIso p (variableChangeCongrOverIso
      (legendreCurve (l : R)) (legendreCurve (1 - ((a⁻¹ : Rˣ) : R)))
      (legendreSwapChange u * legendreReciprocalChange v * legendreSwapChange u)
      (legendreBraidLeft_equation l a u v ha hu hv)) =
    groupCyclicParameterIso p (variableChangeCongrOverIso
      (legendreCurve (l : R)) (legendreCurve (1 - ((a⁻¹ : Rˣ) : R)))
      (legendreReciprocalChange (legendreBraidRoot u v w) * legendreSwapChange u *
        legendreReciprocalChange w)
      (legendreBraidRight_equation l a u v w ha hu hv hw)) :=
  variableChangeCyclic_congr (legendreCurve (l : R)) p
    (legendreCurve (1 - ((a⁻¹ : Rˣ) : R))) _ _ _ _
    (legendreCoordinate_braid u v w hu (by rw [hv, hw, ha]; ring))

/-- Three cyclic coordinate transports compose to transport by their product. -/
theorem variableChangeCyclic_trans_three
    (W V U Z : WeierstrassCurve R)
    [W.IsElliptic] [V.IsElliptic] [U.IsElliptic] [Z.IsElliptic]
    (A B C : VariableChange R)
    (hC : C • W = V) (hB : B • V = U) (hA : A • U = Z) :
    (groupCyclicParameterIso p (variableChangeCongrOverIso U Z A hA) ≪≫
      groupCyclicParameterIso p (variableChangeCongrOverIso V U B hB)) ≪≫
        groupCyclicParameterIso p (variableChangeCongrOverIso W V C hC) =
    groupCyclicParameterIso p (variableChangeCongrOverIso W Z (A * B * C)
      (by rw [mul_smul, hC, mul_smul, hB, hA])) := by
  rw [variableChangeCyclic_trans, variableChangeCyclic_trans]

end WeierstrassCurve.CubicCharts
