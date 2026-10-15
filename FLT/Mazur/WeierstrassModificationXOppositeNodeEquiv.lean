/-
Copyright (c) 2026 krandder. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: krandder
-/
module

public import FLT.Mazur.WeierstrassModificationXNodeDenominators
public import FLT.Mazur.WeierstrassModificationXPolynomialNodeEquiv
public import FLT.Mazur.PrincipalOpenTransport

/-!
# The opposite full original arithmetic node equivalence

Transport through the original reflection constructs both directions of the
opposite comparison. Every original coefficient and smoothing scale is retained.
-/

@[expose] public noncomputable section
open Polynomial
namespace FLT.Mazur.WeierstrassModificationX
variable {R : Type*} [CommRing R] (W : WeierstrassCurve R) (s b3 b4 b6 : R)
  (r : R[X])
local notation "A" => Coordinate W s b3 b4 b6
local notation "O" => PolynomialInitialOpen W s b3 b4 b6 r
local notation "L" => PolynomialNodeOpen W s

/-- The entire reflected original principal open. -/
abbrev PolynomialOppositeInitialOpen :=
  Localization.Away (polynomialOppositeDenominator W s b3 b4 b6 r)

local notation "O'" => PolynomialOppositeInitialOpen W s b3 b4 b6 r

/-- Reflection identifies the two original node neighborhoods before node comparison. -/
def polynomialInitialReflection : O ≃ₐ[R] O' :=
  PrincipalOpenTransport.equiv ((initialReflection W s b3 b4 b6).restrictScalars R)
    (polynomialSmallFactor W s b3 b4 b6 r + algebraMap R A W.a₁)
    (polynomialOppositeDenominator W s b3 b4 b6 r)
    (initialReflection_denominator W s b3 b4 b6 r)

/-- Reflection on the localized opens is the original reflection on every function. -/
theorem polynomialInitialReflection_base (z : A) :
    polynomialInitialReflection W s b3 b4 b6 r (algebraMap A O z) =
      algebraMap A O' (initialReflection W s b3 b4 b6 z) :=
  PrincipalOpenTransport.equiv_base ..

/-- The inverse uses the same reflection on every original function. -/
theorem polynomialInitialReflection_symm_base (z : A) :
    (polynomialInitialReflection W s b3 b4 b6 r).symm (algebraMap A O' z) =
      algebraMap A O (initialReflection W s b3 b4 b6 z) :=
  PrincipalOpenTransport.equiv_symm_base ..

variable (hr : r ^ 2 + polynomialSlopeLinear W b3 * r = polynomialSlopeConstant W b4 b6)
  (I : Ideal R) (hI : IsNilpotent I) (hrI : r ∈ I.map C) (h3 : b3 ∈ I)

/-- The opposite original neighborhood is a full smoothing-node neighborhood. -/
def polynomialOppositeNodeEquiv : O' ≃ₐ[R] L :=
  (polynomialInitialReflection W s b3 b4 b6 r).symm.trans
    (polynomialNodeEquiv W s b3 b4 b6 r hr I hI hrI h3)

/-- The opposite node comparison evaluates every original function by reflection. -/
theorem polynomialOppositeNodeEquiv_base (z : A) :
    polynomialOppositeNodeEquiv W s b3 b4 b6 r hr I hI hrI h3 (algebraMap A O' z) =
      polynomialNodeForwardBase W s b3 b4 b6 r hr I hI hrI h3
        (initialReflection W s b3 b4 b6 z) := by
  change polynomialNodeEquiv W s b3 b4 b6 r hr I hI hrI h3
    ((polynomialInitialReflection W s b3 b4 b6 r).symm (algebraMap A O' z)) = _
  rw [polynomialInitialReflection_symm_base]
  exact polynomialNodeForward_base W s b3 b4 b6 r hr I hI hrI h3 _

end FLT.Mazur.WeierstrassModificationX
