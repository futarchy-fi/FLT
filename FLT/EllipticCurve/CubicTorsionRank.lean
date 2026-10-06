/-
Copyright (c) 2026 krandder. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: krandder
-/
module

public import FLT.EllipticCurve.CubicTorsionClassicalGroup
public import FLT.EllipticCurve.CubicTorsionEtaleAlgebra
public import FLT.EllipticCurve.Torsion
public import FLT.GroupScheme.FiniteFlat

/-! # Dimension of the prime-to-characteristic torsion coordinate fibers -/

open scoped TensorProduct
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
@[expose] public noncomputable section
namespace WeierstrassCurve.CubicCharts
universe u
variable {R : Type u} [CommRing R] (W : WeierstrassCurve R)
variable [IsNoetherianRing R] [_root_.IsReduced R] [W.IsElliptic]

/-- The coordinate fiber has dimension n² when n is nonzero in a separably closed extension. -/
theorem torsionCoordinate_field_finrank (n : ℕ) [NeZero n]
    (K L : Type u) [Field K] [Field L] [IsSepClosed L]
    [Algebra R K] [Algebra K L] [Algebra R L] [IsScalarTower R K L]
    (hn : (n : L) ≠ 0) :
    Module.finrank K (K ⊗[R] torsionCoordinateRing W n) = n ^ 2 := by
  classical
  have hK : (n : K) ≠ 0 := by
    intro h
    apply hn
    simpa using congrArg (algebraMap K L) h
  have : Algebra.Etale K (K ⊗[R] torsionCoordinateRing W n) :=
    torsionCoordinate_field_etale W n K (isUnit_iff_ne_zero.mpr hK)
  calc
    Module.finrank K (K ⊗[R] torsionCoordinateRing W n) =
        Nat.card ((K ⊗[R] torsionCoordinateRing W n) →ₐ[K] L) :=
      GaloisModule.finrank_eq_natCard_algHom K L _
    _ = Nat.card (torsionCoordinateRing W n →ₐ[R] L) :=
      Nat.card_congr (AlgHom.liftEquiv R K (torsionCoordinateRing W n) L).symm
    _ = Nat.card {P : (W.map (algebraMap R L)).toAffine.Point // n • P = 0} :=
      Nat.card_congr ((WithConv.equiv _).symm.trans
        (torsionCoordinateClassicalMulEquiv W L n).toEquiv)
    _ = n ^ 2 :=
      (W.map (algebraMap R L)).card_torsion_of_divisionDifferentialDefect hn
        ((W.map (algebraMap R L)).divisionDifferentialDefect_eq_zero n)

end WeierstrassCurve.CubicCharts
