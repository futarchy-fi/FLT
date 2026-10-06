/-
Copyright (c) 2026 krandder. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: krandder
-/
module

public import FLT.EllipticCurve.CubicTorsionHopfPoints

/-! # Group comparison with classical torsion points -/

open AlgebraicGeometry CategoryTheory
open MonoidalCategory CartesianMonoidalCategory MonObj
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
@[expose] public noncomputable section
namespace WeierstrassCurve.CubicCharts
universe u
variable {R : Type u} [CommRing R] (W : WeierstrassCurve R)
variable [IsNoetherianRing R] [_root_.IsReduced R] [W.IsElliptic]
/-- The represented torsion kernel has the classical torsion group law over fields. -/
def classicalTorsionMulEquiv (K : Type u) [Field K] [Algebra R K]
    [DecidableEq K] (n : ℕ) :
    (pointSource (R := R) K ⟶ torsionModel W n) ≃*
      Multiplicative ((nsmulAddMonoidHom n :
        (W.map (algebraMap R K)).toAffine.Point →+
        (W.map (algebraMap R K)).toAffine.Point).ker) where
  toEquiv := classicalTorsionPointEquiv W K n
  map_mul' f g := by
    apply Subtype.ext
    have h := congrArg Subtype.val
      ((torsionPointMulEquiv W n (pointSource K)).map_mul f g)
    change ((classicalPointEquiv W K).symm
      ((torsionPointMulEquiv W n (pointSource K)) (f * g)).val).toAdd = _
    rw [h]
    exact congrArg Multiplicative.toAdd ((classicalPointEquiv W K).symm.map_mul
      ((torsionPointMulEquiv W n (pointSource K)) f).val
      ((torsionPointMulEquiv W n (pointSource K)) g).val)
/-- Convolution points of the actual Hopf algebra identify with the classical torsion group. -/
def torsionCoordinateClassicalMulEquiv (K : Type u) [Field K] [Algebra R K]
    [DecidableEq K] (n : ℕ) [NeZero n] :
    WithConv (torsionCoordinateRing W n →ₐ[R] K) ≃*
      Multiplicative ((nsmulAddMonoidHom n :
        (W.map (algebraMap R K)).toAffine.Point →+
        (W.map (algebraMap R K)).toAffine.Point).ker) :=
  (hopfPointMulEquivAux (torsionCoordinateRing W n) (torsionModel W n)
    (torsionCoordinateGroupIso W n) K).trans (classicalTorsionMulEquiv W K n)
end WeierstrassCurve.CubicCharts
