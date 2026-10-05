/-
Copyright (c) 2026 krandder. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: krandder
-/
module

public import FLT.Mazur.EllipticProjectiveBaseChange
public import FLT.Mazur.EllipticComponentVariableChange

/-!
# Affine formulas for projective point maps

The existing extension homomorphism and integral variable-change equivalence
act by their expected formulas on affine representatives. Witnesses of
nonsingularity in the target may be supplied independently of the maps.
-/

@[expose] public section

namespace FLT.Mazur

open WeierstrassCurve WeierstrassCurve.Projective

variable {K L : Type*} [Field K] [Field L]

/-- Extension of an affine representative applies the field map to both coordinates. -/
theorem extensionProjectiveHom_some (W : WeierstrassCurve K) (f : K →+* L)
    (V : WeierstrassCurve L) (he : W.map f = V) {x y : K}
    (h : W.toAffine.Nonsingular x y) (h' : V.toAffine.Nonsingular (f x) (f y)) :
    extensionProjectiveHom W f V he (Affine.Point.some x y h).toProjective =
      (Affine.Point.some (f x) (f y) h').toProjective := by
  apply Projective.Point.ext
  change (⟦f ∘ ![x, y, 1]⟧ : Projective.PointClass L) = ⟦![f x, f y, 1]⟧
  simp only [comp_fin3, map_one]

/-- A target equation identified explicitly has the expected nonsingular affine image. -/
theorem extension_nonsingular (W : WeierstrassCurve K) (f : K →+* L)
    (V : WeierstrassCurve L) (he : W.map f = V) {x y : K}
    (h : W.toAffine.Nonsingular x y) : V.toAffine.Nonsingular (f x) (f y) := by
  rw [← he]
  exact (W.toAffine.map_nonsingular f.injective x y).mpr h

variable [DecidableEq K] (A : ValuationSubring K) (W : WeierstrassCurve A)
  (C : VariableChange A) [(W.map (algebraMap A K)).IsElliptic]

/-- The integral projective equivalence has the usual affine coordinate formula. -/
theorem integralProjectiveVariableChange_some {x y : K}
    (h : ((C • W).map (algebraMap A K)).toAffine.Nonsingular x y)
    (h' : (W.map (algebraMap A K)).toAffine.Nonsingular
      ((C.u : K) ^ 2 * x + C.r)
      ((C.u : K) ^ 3 * y + (C.u : K) ^ 2 * C.s * x + C.t)) :
    integralProjectiveVariableChange A W C (Affine.Point.some x y h).toProjective =
      (Affine.Point.some _ _ h').toProjective := by
  change (((Projective.Point.toAffineAddEquiv _).trans
    (integralAffineVariableChange A W C)).trans
    (Projective.Point.toAffineAddEquiv _).symm)
    ((Projective.Point.toAffineAddEquiv _).symm (.some _ _ h)) = _
  simp only [AddEquiv.trans_apply, AddEquiv.apply_symm_apply]
  simp only [integralAffineVariableChange, AddEquiv.trans_apply, Affine.Point.equivOfEq_some,
    Affine.Point.equivVariableChange_some, Projective.Point.toAffineAddEquiv_symm_apply]
  rfl

/-- The inverse equivalence sends transformed affine coordinates back to the source. -/
theorem integralProjectiveVariableChange_symm_some {x y : K}
    (h : ((C • W).map (algebraMap A K)).toAffine.Nonsingular x y)
    (h' : (W.map (algebraMap A K)).toAffine.Nonsingular
      ((C.u : K) ^ 2 * x + C.r)
      ((C.u : K) ^ 3 * y + (C.u : K) ^ 2 * C.s * x + C.t)) :
    (integralProjectiveVariableChange A W C).symm (Affine.Point.some _ _ h').toProjective =
      (Affine.Point.some x y h).toProjective := by
  apply (integralProjectiveVariableChange A W C).injective
  rw [AddEquiv.apply_symm_apply, integralProjectiveVariableChange_some A W C h h']

end FLT.Mazur
