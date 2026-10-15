/-
Copyright (c) 2026 krandder. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: krandder
-/
module

public import FLT.Mazur.WeierstrassModificationXPolynomialNodeEquiv

/-!
# Restriction of original initial maps to the constructed full node

A map on the original functions whose node denominator is a unit factors
through the constructed node, with its actual corrected incidence coordinate.
-/

@[expose] public noncomputable section
open Polynomial
namespace FLT.Mazur.WeierstrassModificationX
variable {R S : Type*} [CommRing R] [CommRing S] [Algebra R S]
  (W : WeierstrassCurve R) (s b3 b4 b6 : R) (r : R[X])
local notation "A" => Coordinate W s b3 b4 b6
local notation "O" => PolynomialInitialOpen W s b3 b4 b6 r
local notation "L" => PolynomialNodeOpen W s
local notation "N" => NodalFiber.Coordinate s
variable (E : Coordinate W s b3 b4 b6 →ₐ[R] S)
  (hu : IsUnit (E (polynomialSmallFactor W s b3 b4 b6 r +
    algebraMap R (Coordinate W s b3 b4 b6) W.a₁)))

/-- Restrict any original evaluation to the actual initial principal neighborhood. -/
def polynomialInitialRestriction : O →ₐ[R] S :=
  IsLocalization.Away.liftAlgHom
    (polynomialSmallFactor W s b3 b4 b6 r + algebraMap R A W.a₁) (f := E) hu

/-- The restriction retains every original function. -/
theorem polynomialInitialRestriction_base (z : A) :
    polynomialInitialRestriction W s b3 b4 b6 r E hu (algebraMap A O z) = E z := by
  rw [polynomialInitialRestriction, IsLocalization.Away.liftAlgHom_apply,
    IsLocalization.Away.lift_eq]
  rfl

variable (hr : r ^ 2 + polynomialSlopeLinear W b3 * r = polynomialSlopeConstant W b4 b6)
  (I : Ideal R) (hI : IsNilpotent I) (hrI : r ∈ I.map C) (h3 : b3 ∈ I)

/-- The actual map from full node functions to the prescribed original target. -/
def polynomialNodeRestriction : L →ₐ[R] S :=
  (polynomialInitialRestriction W s b3 b4 b6 r E hu).comp
    (polynomialNodeEquiv W s b3 b4 b6 r hr I hI hrI h3).symm.toAlgHom

/-- The node restriction evaluates the second node coordinate as the original small factor. -/
theorem polynomialNodeRestriction_q :
    polynomialNodeRestriction W s b3 b4 b6 r E hu hr I hI hrI h3
      (algebraMap N L (NodalFiber.q s)) = E (polynomialSmallFactor W s b3 b4 b6 r) := by
  change polynomialInitialRestriction W s b3 b4 b6 r E hu
    (polynomialNodeBackward W s b3 b4 b6 r hr _) = _
  rw [polynomialNodeBackward_q, polynomialInitialRestriction_base]

/-- The first node coordinate is t times the opposite factor, retaining the parameter change. -/
theorem polynomialNodeRestriction_p :
    polynomialNodeRestriction W s b3 b4 b6 r E hu hr I hI hrI h3
      (algebraMap N L (NodalFiber.p s)) =
        E (t W s b3 b4 b6 * polynomialOppositeFactor W s b3 b4 b6 r) := by
  change polynomialInitialRestriction W s b3 b4 b6 r E hu
    (polynomialNodeBackward W s b3 b4 b6 r hr _) = _
  rw [polynomialNodeBackward_p, ← map_mul, polynomialInitialRestriction_base]

/-- The constructed node restriction composes to the original map on all functions. -/
theorem polynomialNodeRestriction_forward :
    (polynomialNodeRestriction W s b3 b4 b6 r E hu hr I hI hrI h3).comp
      (polynomialNodeForwardBase W s b3 b4 b6 r hr I hI hrI h3) = E := by
  apply AlgHom.ext
  intro z
  change polynomialInitialRestriction W s b3 b4 b6 r E hu
    ((polynomialNodeEquiv W s b3 b4 b6 r hr I hI hrI h3).symm
      (polynomialNodeForwardBase W s b3 b4 b6 r hr I hI hrI h3 z)) = E z
  rw [← polynomialNodeForward_base W s b3 b4 b6 r hr I hI hrI h3 z]
  change polynomialInitialRestriction W s b3 b4 b6 r E hu
    ((polynomialNodeEquiv W s b3 b4 b6 r hr I hI hrI h3).symm
      (polynomialNodeEquiv W s b3 b4 b6 r hr I hI hrI h3 (algebraMap A O z))) = E z
  rw [AlgEquiv.symm_apply_apply, polynomialInitialRestriction_base]

end FLT.Mazur.WeierstrassModificationX
