/-
Copyright (c) 2026 krandder. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: krandder
-/
module

public import FLT.EllipticCurve.CubicTorsionGroup
public import Mathlib.AlgebraicGeometry.Group.Affine

/-! # The actual finite coordinate Hopf algebra of cubic torsion -/

@[expose] public noncomputable section
open AlgebraicGeometry CategoryTheory CategoryTheory.Limits
open MonoidalCategory CartesianMonoidalCategory MonObj
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true

namespace WeierstrassCurve.CubicCharts
universe u
variable {R : Type u} [CommRing R] (W : WeierstrassCurve R)
variable [IsNoetherianRing R] [_root_.IsReduced R] [W.IsElliptic]

instance torsionModelFinite (n : ℕ) [NeZero n] :
    IsFinite (torsionModel W n).hom := torsionModel_finite W (NeZero.ne n)

instance torsionModelAffine (n : ℕ) [NeZero n] :
    IsAffine (torsionModel W n).left :=
  isAffine_of_isAffineHom (torsionModel W n).hom

instance torsionModelAsOverGrpObj (n : ℕ) :
    GrpObj ((torsionModel W n).left.asOver (Spec (.of R))) := by
  change GrpObj (torsionModel W n)
  infer_instance

/-- The actual global-section ring of the represented nonzero-order torsion scheme. -/
abbrev torsionCoordinateRing (n : ℕ) := Γ((torsionModel W n).left, ⊤)

instance torsionCoordinateAlgebra (n : ℕ) [NeZero n] :
    Algebra R (torsionCoordinateRing W n) :=
  instAlgebraCarrierObjOppositeOpensCarrierCarrierCommRingCatPresheafOpOpensTopOfOverSpecOfIsAffine
    (R := .of R) (X := (torsionModel W n).left)

instance torsionCoordinateHopfAlgebra (n : ℕ) [NeZero n] :
    HopfAlgebra R (torsionCoordinateRing W n) := by
  letI : (algSpec (.of R)).Braided := braidedAlgSpec (R := .of R)
  let G := (torsionModel W n).left
  have : GrpObj ((algSpec (.of R)).obj (.op (CommAlgCat.of R (torsionCoordinateRing W n)))) :=
    .ofIso (G.isoSpec.asOver (Spec (.of R)))
  have : GrpObj (Opposite.op (CommAlgCat.of R (torsionCoordinateRing W n))) :=
    (algSpec.fullyFaithful (R := .of R)).grpObj
      (Opposite.op (CommAlgCat.of R (torsionCoordinateRing W n)))
  exact ((commHopfAlgCatEquivCogrpCommAlgCat R).inverse.obj
    (.op (.mk (Opposite.op (CommAlgCat.of R (torsionCoordinateRing W n)))))).hopfAlgebra

/-- The actual coordinate Hopf algebra is finite as a module over the base. -/
theorem torsionCoordinateRing_finite (n : ℕ) [NeZero n] :
    Module.Finite R (torsionCoordinateRing W n) := by
  apply RingHom.finite_algebraMap.mp
  apply (IsFinite.SpecMap_iff (CommRingCat.ofHom
    (algebraMap R (torsionCoordinateRing W n)))).mp
  change IsFinite (Spec.map (Spec.fullyFaithful.preimage
    ((torsionModel W n).left.isoSpec.inv ≫ (torsionModel W n).hom)).unop)
  change IsFinite (Scheme.Spec.map (Spec.fullyFaithful.preimage
    ((torsionModel W n).left.isoSpec.inv ≫ (torsionModel W n).hom)))
  rw [Spec.fullyFaithful.map_preimage]
  infer_instance

/-- The spectrum of the coordinate Hopf algebra is the constructed torsion scheme. -/
def torsionCoordinateSpecIso (n : ℕ) [NeZero n] :
    (torsionModel W n).left ≅ Spec (torsionCoordinateRing W n) :=
  (torsionModel W n).left.isoSpec

end WeierstrassCurve.CubicCharts
