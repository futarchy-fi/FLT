/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.RootsOfUnityAlgebraPoints
public import Mathlib.RingTheory.AdjoinRoot

/-!
# Polynomial presentation of the roots-of-unity coordinates

The character Hopf algebra is identified with R[X]/(X^n - 1). The two maps
retain the actual universal root. This connects the finite group construction
to the monic equation used for its Cartier divisor geometry.
-/

@[expose] public noncomputable section

set_option backward.isDefEq.respectTransparency false

open Polynomial

namespace FLT.Mazur.RootsOfUnityPolynomialPresentation

open RootsOfUnityAlgebra RootsOfUnityAlgebraPoints

variable (R : Type*) [CommRing R] (n : ℕ) [NeZero n]

/-- The monic equation defining nth roots of unity. -/
def equation : R[X] := X ^ n - 1

omit [NeZero n] in
/-- The class of X satisfies the nth-power equation. -/
theorem quotientRoot_pow : AdjoinRoot.root (equation R n) ^ n = 1 := by
  have h : AdjoinRoot.mk (equation R n) (X ^ n - 1) = 0 :=
    AdjoinRoot.mk_self
  simpa only [map_sub, map_pow, AdjoinRoot.mk_X, map_one, sub_eq_zero] using h

/-- The polynomial coordinate is a unit, without assuming n invertible. -/
def quotientRootUnit : (AdjoinRoot (equation R n))ˣ :=
  Units.ofPowEqOne _ n (quotientRoot_pow R n) (NeZero.ne n)

/-- Send the polynomial coordinate to the universal character. -/
def toCharacter : AdjoinRoot (equation R n) →ₐ[R] Coordinate R n :=
  AdjoinRoot.liftAlgHom _ (Algebra.ofId R _) (rootUnit R n).val (by
    have h := congrArg Units.val (rootUnit_pow R n)
    simpa only [equation, eval₂_sub, eval₂_pow, eval₂_X, eval₂_one,
      sub_eq_zero, Units.val_pow_eq_pow_val, Units.val_one] using h)

omit [NeZero n] in
@[simp]
theorem toCharacter_root :
    toCharacter R n (AdjoinRoot.root (equation R n)) = (rootUnit R n).val :=
  AdjoinRoot.liftAlgHom_root _ _ _ _

/-- Send the character to the invertible polynomial coordinate. -/
def toPolynomial : Coordinate R n →ₐ[R] AdjoinRoot (equation R n) :=
  evalRoot n (quotientRootUnit R n)
    (Units.pow_ofPowEqOne (quotientRoot_pow R n) (NeZero.ne n))

@[simp]
theorem toPolynomial_root :
    toPolynomial R n (rootUnit R n).val = AdjoinRoot.root (equation R n) := by
  change evalRoot n (quotientRootUnit R n) _
    (AddMonoidAlgebra.single 1 1) = (quotientRootUnit R n).val
  simpa only [pow_one, Nat.cast_one] using
    evalRoot_natCast (R := R) n (quotientRootUnit R n)
      (Units.pow_ofPowEqOne (quotientRoot_pow R n) (NeZero.ne n)) 1

/-- The polynomial and character coordinate rings are inverse presentations. -/
def coordinateEquiv : AdjoinRoot (equation R n) ≃ₐ[R] Coordinate R n :=
  AlgEquiv.ofAlgHom (toCharacter R n) (toPolynomial R n)
    (by
      apply RootsOfUnityAlgebraPoints.hom_ext n
      simp only [AlgHom.comp_apply, toPolynomial_root, toCharacter_root, AlgHom.id_apply])
    (by
      apply AdjoinRoot.algHom_ext
      simp only [AlgHom.comp_apply, toCharacter_root, toPolynomial_root, AlgHom.id_apply])

/-- The equivalence retains X as the universal root of unity. -/
theorem coordinateEquiv_root :
    coordinateEquiv R n (AdjoinRoot.root (equation R n)) = (rootUnit R n).val :=
  toCharacter_root R n

/-- The inverse equivalence retains the same coordinate. -/
theorem coordinateEquiv_symm_root :
    (coordinateEquiv R n).symm (rootUnit R n).val = AdjoinRoot.root (equation R n) :=
  toPolynomial_root R n

end FLT.Mazur.RootsOfUnityPolynomialPresentation
