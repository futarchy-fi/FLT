/-
Copyright (c) 2026 krandder. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: krandder
-/
module

public import FLT.Mazur.WeierstrassDilatationCoefficients

/-!
# Original ring homomorphisms on the full terminal cubic

An arbitrary coefficient homomorphism induces the full divided cubic map,
preserving the original horizontal and vertical coordinates.
-/

@[expose] public noncomputable section
namespace FLT.Mazur.WeierstrassDilatation
variable {R S : Type*} [CommRing R] [CommRing S] (f : R →+* S)
  (W : WeierstrassCurve R) (s b3 b4 b6 : R)

/-- The entire divided cubic map induced by a specified coefficient homomorphism. -/
def coefficientRingMap : Coordinate W s b3 b4 b6 →+*
    Coordinate (W.map f) (f s) (f b3) (f b4) (f b6) := by
  letI := f.toAlgebra
  exact (coefficientMap W s b3 b4 b6 S).toRingHom

/-- The horizontal coordinate retains its original value under coefficient change. -/
@[simp] theorem coefficientRingMap_x :
    coefficientRingMap f W s b3 b4 b6 (x W s b3 b4 b6) =
      x (W.map f) (f s) (f b3) (f b4) (f b6) := by
  let _ := f.toAlgebra
  exact coefficientMap_x W s b3 b4 b6 S

/-- The vertical coordinate retains its original value under coefficient change. -/
@[simp] theorem coefficientRingMap_y :
    coefficientRingMap f W s b3 b4 b6 (y W s b3 b4 b6) =
      y (W.map f) (f s) (f b3) (f b4) (f b6) := by
  let _ := f.toAlgebra
  exact coefficientMap_y W s b3 b4 b6 S

/-- Original scalars follow exactly the specified coefficient homomorphism. -/
@[simp] theorem coefficientRingMap_algebraMap (a : R) :
    coefficientRingMap f W s b3 b4 b6 (algebraMap R _ a) = algebraMap S _ (f a) := by
  let _ := f.toAlgebra
  change (coefficientMap W s b3 b4 b6 S).toRingHom (algebraMap R _ a) = _
  rw [AlgHom.toRingHom_eq_coe, AlgHom.coe_toRingHom, AlgHom.commutes,
    IsScalarTower.algebraMap_apply R S]
  rfl

end FLT.Mazur.WeierstrassDilatation
