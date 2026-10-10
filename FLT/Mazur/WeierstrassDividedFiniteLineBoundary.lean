/-
Copyright (c) 2026 krandder. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: krandder
-/
module

public import FLT.Mazur.WeierstrassDividedFiniteLineContractions
public import FLT.Mazur.WeierstrassDividedPreviousBoundaryAlgebra
public import FLT.Mazur.PrincipalOpenTensorTransitionBase
public import FLT.Mazur.WeierstrassSuccessiveXResidueLineLocalization

/-!
# Horizontal line maps through the actual preceding boundary

The whole localized line map is transported through the integral parameter
identification and horizontal equivalence. Its restriction agrees on every
function with the original preceding tensor contraction.
-/

@[expose] public noncomputable section
open IsLocalRing Polynomial
open scoped TensorProduct LaurentPolynomial
namespace FLT.Mazur.WeierstrassDividedDepth
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
variable {R : Type*} [CommRing R] [IsDomain R] [IsLocalRing R]
  {W : WeierstrassCurve R} {π : R} (hπ : π ≠ 0) {start n depth : ℕ}
  (data : (i : Fin (n + 1)) → Data W π (start + i.val))
  (D : SplitNodeDepth W π depth) (j : ℕ) (hj : j + 1 ≤ n)
  (hk0 : 0 < start + j) (hk : 2 * (start + j + 1) ≤ depth)
open WeierstrassSuccessiveX
local notation "K" => ResidueField R
local notation "d" => data (Fin.mk j (Nat.lt_succ_of_le (Nat.le_of_succ_le hj)))
local notation "e" => data (Fin.mk (j + 1) (Nat.lt_succ_of_le hj))
local notation "A" => WeierstrassDilatation.Coordinate W (π ^ (start + j))
  (Data.b3 d) (Data.b4 d) (Data.b6 d)
local notation "T" => WeierstrassDilatation.ScalarExtension W (π ^ (start + j))
  (Data.b3 d) (Data.b4 d) (Data.b6 d) K
local notation "p" => WeierstrassDilatation.parameterEquiv W (π ^ (start + j))
  (π ^ (start + j)) (Data.b3 d) (Data.b4 d) (Data.b6 d)
  (π * Data.b3 e) (π * Data.b4 e) (π ^ 2 * Data.b6 e) rfl
  (factor3_step hπ d e) (factor4_step hπ d e) (factor6_step hπ d e)
local notation "f" => tensorPreviousMap W (π ^ (start + j)) π
  (Data.b3 e) (Data.b4 e) (Data.b6 e) K
local notation "tx" => WeierstrassDilatation.tensorX W (π ^ (start + j))
  (Data.b3 d) (Data.b4 d) (Data.b6 d) K
local notation "ty" => WeierstrassDilatation.tensorY W (π ^ (start + j))
  (Data.b3 d) (Data.b4 d) (Data.b6 d) K
variable (r : ResidueField R) (hr : r * (r + residue R W.a₁) = 0)
local notation "L" => residueSuccessiveLineMap D (start + j) hk0 hk
  (Data.b3 e) (Data.b4 e) (Data.b6 e) (Data.factor3 e) (Data.factor4 e) r hr


local notation "x" => WeierstrassDilatation.x W (π ^ (start + j))
  (Data.b3 d) (Data.b4 d) (Data.b6 d)
local notation "u" => coord W (π ^ (start + j)) π (Data.b3 e) (Data.b4 e) (Data.b6 e) 2
local notation "a" => previousBoundaryEquiv hπ d e
local notation "φ" => residueFiniteLineContraction hπ data D j hj hk0 hk r hr

/-- The full line map on the actual preceding horizontal tensor localization. -/
def residueFiniteLineBoundaryMap : Localization.Away tx →ₐ[K] K[T;T⁻¹] :=
  (residueLineHorizontalMap D (start + j) hk0 hk (Data.b3 e) (Data.b4 e)
    (Data.b6 e) (Data.factor3 e) (Data.factor4 e) r hr).comp
      (PrincipalOpenTensor.transition K x u a).toAlgHom

/-- Pure tensors retain their full original line restrictions across the boundary. -/
theorem residueFiniteLineBoundaryMap_tmul_base (s : K) (z : A) :
    residueFiniteLineBoundaryMap hπ data D j hj hk0 hk r hr
      (algebraMap T (Localization.Away tx) (s ⊗ₜ[R] z)) =
        Polynomial.toLaurent (φ (s ⊗ₜ[R] z)) := by
  have H := PrincipalOpenTensor.transition_tmul_base K x u a
    ((fromDivided W (π ^ (start + j)) π (Data.b3 e) (Data.b4 e)
      (Data.b6 e)).comp (AlgEquiv.toAlgHom p)) (previousBoundaryEquiv_base hπ d e) s z
  have H' := congrArg (residueLineHorizontalMap D (start + j) hk0 hk
    (Data.b3 e) (Data.b4 e) (Data.b6 e) (Data.factor3 e) (Data.factor4 e) r hr) H
  refine H'.trans ?_
  refine (residueLineHorizontalMap_base D (start + j) hk0 hk
    (Data.b3 e) (Data.b4 e) (Data.b6 e) (Data.factor3 e) (Data.factor4 e) r hr
      (s ⊗ₜ[R] fromDivided W (π ^ (start + j)) π
        (Data.b3 e) (Data.b4 e) (Data.b6 e) (p z))).trans ?_
  change Polynomial.toLaurent (L (s ⊗ₜ[R] _)) =
    Polynomial.toLaurent (s • L ((1 : K) ⊗ₜ[R] _))
  rw [← map_smul, TensorProduct.smul_tmul', smul_eq_mul, mul_one]
  rfl

/-- All tensor functions restrict by the original parameter-corrected contraction. -/
@[simp] theorem residueFiniteLineBoundaryMap_base (z : T) :
    residueFiniteLineBoundaryMap hπ data D j hj hk0 hk r hr
      (algebraMap T (Localization.Away tx) z) = Polynomial.toLaurent (φ z) := by
  induction z using TensorProduct.inductionOn with
  | tmul s z => exact residueFiniteLineBoundaryMap_tmul_base hπ data D j hj hk0 hk r hr s z
  | add z w hz hw => simp only [map_add, hz, hw]

/-- The inverse preceding horizontal coordinate remains the original inverse line parameter. -/
theorem residueFiniteLineBoundaryMap_inverse :
    residueFiniteLineBoundaryMap hπ data D j hj hk0 hk r hr
      (IsLocalization.Away.invSelf tx) = LaurentPolynomial.T (-1) := by
  have h := congrArg (residueFiniteLineBoundaryMap hπ data D j hj hk0 hk r hr)
    (IsLocalization.Away.mul_invSelf (S := Localization.Away tx) tx)
  rw [map_mul, map_one, residueFiniteLineBoundaryMap_base,
    residueFiniteLineContraction_x, Polynomial.toLaurent_X] at h
  apply (LaurentPolynomial.isUnit_T (R := K) 1).mul_left_cancel
  exact h.trans (by rw [← LaurentPolynomial.T_add]; rfl)

end FLT.Mazur.WeierstrassDividedDepth
