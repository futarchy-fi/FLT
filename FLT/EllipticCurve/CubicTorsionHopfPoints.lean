/-
Copyright (c) 2026 krandder. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: krandder
-/
module

public import FLT.EllipticCurve.CubicTorsionHopfComparison

/-! # Algebra-valued points of the actual torsion Hopf algebra -/

@[expose] public noncomputable section
open AlgebraicGeometry CategoryTheory CategoryTheory.Limits Opposite
open MonoidalCategory CartesianMonoidalCategory MonObj
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true

namespace WeierstrassCurve.CubicCharts
universe u
variable {R : Type u} [CommRing R] (W : WeierstrassCurve R)
variable [IsNoetherianRing R] [_root_.IsReduced R] [W.IsElliptic]

/-- A Hopf spectrum comparison identifies convolution with geometric point multiplication. -/
def hopfPointMulEquivAux (A : Type u) [CommRing A] [HopfAlgebra R A]
    (G : Over (Spec (.of R))) [GrpObj G]
    (e : Grp.mk G ≅ (hopfSpec (.of R)).obj (op (CommHopfAlgCat.of R A)))
    (B : Type u) [CommRing B] [Algebra R B] :
    WithConv (A →ₐ[R] B) ≃* (pointSource B ⟶ G) := by
  let e' : (Spec (.of A)).asOver (Spec (.of R)) ≅ G :=
    (Grp.forget (Over (Spec (.of R)))).mapIso e.symm
  letI : IsMonHom e'.hom := e.inv.hom.isMonHom_hom
  exact Spec.mapMulEquiv.trans (Hom.mulEquivCongrRight e' (pointSource B))

/-- Convolution points are exactly the represented torsion points, with their group law. -/
def torsionCoordinatePointMulEquiv (n : ℕ) [NeZero n]
    (B : Type u) [CommRing B] [Algebra R B] :
    WithConv (torsionCoordinateRing W n →ₐ[R] B) ≃*
      torsionPointGroup W n (pointSource B) :=
  (hopfPointMulEquivAux (torsionCoordinateRing W n) (torsionModel W n)
    (torsionCoordinateGroupIso W n) B).trans
      (torsionPointMulEquiv W n (pointSource B))

/-- Every algebra-valued point of the coordinate Hopf algebra is killed by its torsion order. -/
theorem torsionCoordinatePoint_pow_eq_one (n : ℕ) [NeZero n]
    (B : Type u) [CommRing B] [Algebra R B]
    (f : WithConv (torsionCoordinateRing W n →ₐ[R] B)) : f ^ n = 1 := by
  apply (torsionCoordinatePointMulEquiv W n B).injective
  rw [map_pow, map_one]
  apply Subtype.ext
  exact (torsionCoordinatePointMulEquiv W n B f).property

/-- Convolution on algebra-valued points is commutative. -/
theorem torsionCoordinatePoint_mul_comm (n : ℕ) [NeZero n]
    (B : Type u) [CommRing B] [Algebra R B]
    (f g : WithConv (torsionCoordinateRing W n →ₐ[R] B)) : f * g = g * f := by
  apply (torsionCoordinatePointMulEquiv W n B).injective
  simp only [map_mul, mul_comm]

end WeierstrassCurve.CubicCharts
