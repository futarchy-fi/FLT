/-
Copyright (c) 2026 krandder. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: krandder
-/
module

public import FLT.Mazur.WeierstrassModificationXPolynomialNodeBackward

/-!
# The full initial arithmetic node equivalence

The two maps are inverse on every function. Uniqueness of the inverse
incidence equation identifies the original t, including at the node itself.
-/

@[expose] public noncomputable section
open Polynomial
namespace FLT.Mazur.WeierstrassModificationX
variable {R : Type*} [CommRing R] (W : WeierstrassCurve R) (s b3 b4 b6 : R)
  (r : R[X]) (hr : r ^ 2 + polynomialSlopeLinear W b3 * r =
    polynomialSlopeConstant W b4 b6)
  (I : Ideal R) (hI : IsNilpotent I) (hrI : r ∈ I.map C) (h3 : b3 ∈ I)
local notation "A" => Coordinate W s b3 b4 b6
local notation "N" => NodalFiber.Coordinate s
local notation "L" => PolynomialNodeOpen W s
local notation "O" => PolynomialInitialOpen W s b3 b4 b6 r
local notation "f" => polynomialNodeForward W s b3 b4 b6 r hr I hI hrI h3
local notation "g" => polynomialNodeBackward W s b3 b4 b6 r hr
local notation "P" => algebraMap N L (NodalFiber.p s)
local notation "Q" => algebraMap N L (NodalFiber.q s)
local notation "T" => polynomialNodeInverseT b3 r I hI hrI h3 W P Q
  (polynomialNodeOpen_unit W s)
local notation "t₀" => algebraMap A O (t W s b3 b4 b6)
local notation "v₀" => algebraMap A O (v W s b3 b4 b6)
local notation "U" => algebraMap A O (polynomialOppositeFactor W s b3 b4 b6 r)
local notation "V" => algebraMap A O (polynomialSmallFactor W s b3 b4 b6 r)

/-- The composite fixes every function of the full localized smoothing node. -/
theorem polynomialNodeForward_backward : (f).comp g = AlgHom.id R L := by
  apply IsLocalization.algHom_ext
    (Submonoid.powers (NodalFiber.q s + algebraMap R N W.a₁))
  apply NodalFiber.hom_ext
  · change f (g P) = P
    rw [polynomialNodeBackward_p, ← map_mul, polynomialNodeForward_base]
    exact polynomialNodeEvaluation_first W s b3 b4 b6 r hr I hI hrI h3 P Q
      (polynomialNodeOpen_unit W s) (polynomialNodeOpen_relation W s)
  · change f (g Q) = Q
    rw [polynomialNodeBackward_q, polynomialNodeForward_base]
    exact polynomialNodeEvaluation_small W s b3 b4 b6 r hr I hI hrI h3 P Q
      (polynomialNodeOpen_unit W s) (polynomialNodeOpen_relation W s)

/-- The reverse map sends the constructed inverse incidence to the original t. -/
theorem polynomialNodeBackward_inverseT : g T = t₀ := by
  have h := congrArg g (polynomialNodeInverseT_equation b3 r I hI hrI h3 W P Q
    (polynomialNodeOpen_unit W s))
  simp only [map_mul, map_add, AlgHom.commutes, Polynomial.algHom_eval₂_algebraMap,
    polynomialNodeBackward_p, polynomialNodeBackward_q] at h
  apply polynomialNodeParameter_unique b3 r I hI hrI h3 W (t₀ * U) V
    (polynomialInitialOpen_unit W s b3 b4 b6 r)
  · exact h
  · exact polynomialInitialOpen_parameter W s b3 b4 b6 r

/-- The composite fixes the entire original initial node neighborhood. -/
theorem polynomialNodeBackward_forward : (g).comp f = AlgHom.id R O := by
  apply IsLocalization.algHom_ext
    (Submonoid.powers (polynomialSmallFactor W s b3 b4 b6 r + algebraMap R A W.a₁))
  apply hom_ext
  · change g (f t₀) = t₀
    rw [polynomialNodeForward_base]
    change g (polynomialNodeEvaluation W s b3 b4 b6 r hr I hI hrI h3 P Q _ _ _) = t₀
    rw [polynomialNodeEvaluation_t, polynomialNodeBackward_inverseT]
  · change g (f v₀) = v₀
    rw [polynomialNodeForward_base]
    change g (polynomialNodeEvaluation W s b3 b4 b6 r hr I hI hrI h3 P Q _ _ _) = v₀
    rw [polynomialNodeEvaluation_v, map_add, polynomialNodeBackward_q,
      Polynomial.algHom_eval₂_algebraMap, polynomialNodeBackward_inverseT]
    have h := hom_polynomial_incidence W s b3 b4 b6 (Algebra.algHom R A O) r
    change algebraMap A O (algebraMap R[X] A r) =
      r.eval₂ (algebraMap R O) t₀ at h
    rw [← h]
    simp only [polynomialSmallFactor, map_sub, sub_add_cancel]

/-- The actual initial arithmetic node open is isomorphic to the original smoothing node open. -/
def polynomialNodeEquiv : O ≃ₐ[R] L :=
  AlgEquiv.ofAlgHom f g
    (polynomialNodeForward_backward W s b3 b4 b6 r hr I hI hrI h3)
    (polynomialNodeBackward_forward W s b3 b4 b6 r hr I hI hrI h3)

end FLT.Mazur.WeierstrassModificationX
