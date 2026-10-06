/-
Copyright (c) 2026 krandder. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: krandder
-/
module

public import FLT.EllipticCurve.CubicTorsionHopf

/-! # Compatibility of the coordinate Hopf algebra with the actual torsion group -/

@[expose] public noncomputable section
open AlgebraicGeometry CategoryTheory CategoryTheory.Limits Opposite
open MonoidalCategory CartesianMonoidalCategory MonObj
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true

namespace WeierstrassCurve.CubicCharts
universe u
variable {R : Type u} [CommRing R] (W : WeierstrassCurve R)
variable [IsNoetherianRing R] [_root_.IsReduced R] [W.IsElliptic]

/-- The spectrum functor preserves the symmetric monoidal structure. -/
local instance coordinateAlgSpecBraided : (algSpec (.of R)).Braided :=
  braidedAlgSpec (R := .of R)

/-- Recover a group object after transporting it through the fully faithful spectrum functor. -/
def coordinateImageIsoAux (G : Over (Spec (.of R))) [GrpObj G]
    (S : CommAlgCat R) (e : G ≅ (algSpec (.of R)).obj (op S)) :
    letI : GrpObj ((algSpec (.of R)).obj (op S)) := .ofIso e
    letI : GrpObj (op S) := (algSpec.fullyFaithful (R := .of R)).grpObj (op S)
    (algSpec (.of R)).mapGrp.obj (Grp.mk (op S)) ≅ Grp.mk G := by
  dsimp only
  refine Grp.mkIso e.symm ?_ ?_ <;> simp [MonObj.ofIso_one, MonObj.ofIso_mul]

/-- The transported coordinate cogroup maps back to the original torsion group. -/
def torsionCoordinateImageIso (n : ℕ) [NeZero n] :
    (algSpec (.of R)).mapGrp.obj (torsionCoordinateCogrp W n) ≅
      Grp.mk (torsionModel W n) :=
  coordinateImageIsoAux (torsionModel W n)
    (CommAlgCat.of R (torsionCoordinateRing W n))
    ((torsionModel W n).left.isoSpec.asOver (Spec (.of R)))

/-- The coordinate Hopf spectrum identifies the actual torsion group, including its law. -/
def torsionCoordinateGroupIso (n : ℕ) [NeZero n] :
    Grp.mk (torsionModel W n) ≅
      (hopfSpec (.of R)).obj (.op (CommHopfAlgCat.of R (torsionCoordinateRing W n))) := by
  let ec := (algSpec (.of R)).mapGrp.mapIso
    (((commHopfAlgCatEquivCogrpCommAlgCat R).counitIso.app
      (op (torsionCoordinateCogrp W n))).unop.symm)
  exact (torsionCoordinateImageIso W n).symm ≪≫ ec.symm

end WeierstrassCurve.CubicCharts
