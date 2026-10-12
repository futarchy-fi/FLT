/-
Copyright (c) 2026 krandder. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: krandder
-/
module

public import FLT.Mazur.WeierstrassCoefficientShearFiniteLineContraction
public import FLT.Mazur.WeierstrassSuccessiveShearLineOpen
public import FLT.Mazur.PrincipalOpenTensorTransitionBase
public import FLT.Mazur.WeierstrassDividedPreviousBoundaryAlgebra
public import FLT.Mazur.WeierstrassDividedDepthData
public import FLT.Mazur.WeierstrassDilatationResidueRetained

/-!
# Arbitrary-root lines on the original preceding tensor boundary

Both the complete tensor restriction and inverse horizontal coordinate are
preserved through the actual integral overlap after coefficient extension.
-/

@[expose] public noncomputable section
open Polynomial
open scoped TensorProduct LaurentPolynomial
namespace FLT.Mazur.WeierstrassDividedDepth
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
universe u
variable {R : Type u} [CommRing R] [IsDomain R]
  {W : WeierstrassCurve R} {π : R} (hπ : π ≠ 0) {k : ℕ}
  (d : Data W π k) (e : Data W π (k + 1))
  (S : Type u) [CommRing S] [Algebra R S] (r : S)
  (hs : algebraMap R S (π ^ k) = 0) (hp : algebraMap R S π = 0)
  (h3 : algebraMap R S e.b3 = 0) (h4 : algebraMap R S e.b4 = 0)
  (hr : r ^ 2 + algebraMap R S W.a₁ * r - algebraMap R S W.a₂ = 0)
open WeierstrassSuccessiveX
local notation "A" => WeierstrassDilatation.Coordinate W (π ^ k)
  (Data.b3 d) (Data.b4 d) (Data.b6 d)
local notation "T" => WeierstrassDilatation.ScalarExtension W (π ^ k)
  (Data.b3 d) (Data.b4 d) (Data.b6 d) S
local notation "p" => WeierstrassDilatation.parameterEquiv W (π ^ k)
  (π ^ k) (Data.b3 d) (Data.b4 d) (Data.b6 d)
  (π * Data.b3 e) (π * Data.b4 e) (π ^ 2 * Data.b6 e) rfl
  (factor3_step hπ d e) (factor4_step hπ d e) (factor6_step hπ d e)
local notation "f" => tensorPreviousMap W (π ^ k) π
  (Data.b3 e) (Data.b4 e) (Data.b6 e) S
local notation "tx" => WeierstrassDilatation.tensorX W (π ^ k)
  (Data.b3 d) (Data.b4 d) (Data.b6 d) S
local notation "ty" => WeierstrassDilatation.tensorY W (π ^ k)
  (Data.b3 d) (Data.b4 d) (Data.b6 d) S
variable (v : S) (hv : v * (v + (rootShearCurve (W.map (algebraMap R S)) r).a₁) = 0)
local notation "L" => tensorShearLineMap W (π ^ k) π
  (Data.b3 e) (Data.b4 e) (Data.b6 e) S r hs hp h3 h4 hr v hv

local notation "x" => WeierstrassDilatation.x W (π ^ k) d.b3 d.b4 d.b6
local notation "u" => coord W (π ^ k) π e.b3 e.b4 e.b6 2
local notation "E" => PrincipalOpenTensor.transition S x u (previousBoundaryEquiv hπ d e)
local notation "l" => tensorShearLineOpenMap W (π ^ k) π
  e.b3 e.b4 e.b6 S r hs hp h3 h4 hr v hv
local notation "φ" => tensorShearFiniteLineContraction hπ d e S r hs hp h3 h4 hr v hv

/-- The full coefficient-split line restriction through the actual previous boundary. -/
@[irreducible] def coefficientShearFiniteLineBoundaryMap :
    Localization.Away tx →ₐ[S] S[T;T⁻¹] := (l).comp (E).toAlgHom

/-- Every pure tensor keeps its parameter-corrected original line restriction. -/
theorem coefficientShearFiniteLineBoundaryMap_tmul_base (s : S) (z : A) :
    coefficientShearFiniteLineBoundaryMap hπ d e S r hs hp h3 h4 hr v hv
      (algebraMap T (Localization.Away tx) (s ⊗ₜ[R] z)) = Polynomial.toLaurent (φ (s ⊗ₜ[R] z)) := by
  rw [coefficientShearFiniteLineBoundaryMap]
  change l (E _) = _
  have H := PrincipalOpenTensor.transition_tmul_base S x u (previousBoundaryEquiv hπ d e)
    ((fromDivided W (π ^ k) π e.b3 e.b4 e.b6).comp (p).toAlgHom)
    (previousBoundaryEquiv_base hπ d e) s z
  erw [H, tensorShearLineOpenMap_base]
  change Polynomial.toLaurent (L (s ⊗ₜ[R] _)) =
    Polynomial.toLaurent (s • L ((1 : S) ⊗ₜ[R] _))
  rw [← map_smul, TensorProduct.smul_tmul', smul_eq_mul, mul_one]
  rfl

/-- Every function on the preceding tensor chart keeps the same line restriction. -/
theorem coefficientShearFiniteLineBoundaryMap_base (z : T) :
    coefficientShearFiniteLineBoundaryMap hπ d e S r hs hp h3 h4 hr v hv
      (algebraMap T (Localization.Away tx) z) = Polynomial.toLaurent (φ z) := by
  induction z using TensorProduct.inductionOn with
  | tmul s z =>
    exact coefficientShearFiniteLineBoundaryMap_tmul_base hπ d e S r hs hp h3 h4 hr v hv s z
  | add z w hz hw => simp only [map_add, hz, hw]

/-- The original inverse horizontal coordinate remains the inverse Laurent parameter. -/
theorem coefficientShearFiniteLineBoundaryMap_inverse :
    coefficientShearFiniteLineBoundaryMap hπ d e S r hs hp h3 h4 hr v hv
      (IsLocalization.Away.invSelf tx) = LaurentPolynomial.T (-1) := by
  have h := congrArg (coefficientShearFiniteLineBoundaryMap hπ d e S r hs hp h3 h4 hr v hv)
    (IsLocalization.Away.mul_invSelf (S := Localization.Away tx) tx)
  rw [map_mul, map_one, coefficientShearFiniteLineBoundaryMap_base,
    tensorShearFiniteLineContraction_x, Polynomial.toLaurent_X] at h
  apply (LaurentPolynomial.isUnit_T (R := S) 1).mul_left_cancel
  exact h.trans (by rw [← LaurentPolynomial.T_add]; rfl)

end FLT.Mazur.WeierstrassDividedDepth
