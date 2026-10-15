/-
Copyright (c) 2026 krandder. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: krandder
-/
module

public import FLT.Mazur.WeierstrassDilatationCoefficientRingMap

/-!
# Explicit coefficient transport of the entire divided cubic

Naming equal target coefficients avoids reducing quotient maps inside large
normalization constructions. The map still preserves every original coordinate.
-/

@[expose] public noncomputable section
namespace FLT.Mazur.WeierstrassDilatation
variable {R S : Type*} [CommRing R] [CommRing S] (f : R →+* S)
  (W : WeierstrassCurve R) (s b3 b4 b6 : R)
  (U : WeierstrassCurve S) (t c3 c4 c6 : S)
  (hW : W.map f = U) (hs : f s = t) (h3 : f b3 = c3)
  (h4 : f b4 = c4) (h6 : f b6 = c6)

/-- The original coefficient map with explicitly identified target coefficients. -/
def coefficientRingMapTo : Coordinate W s b3 b4 b6 →+* Coordinate U t c3 c4 c6 := by
  subst U t c3 c4 c6
  exact coefficientRingMap f W s b3 b4 b6

/-- Explicit transport retains the complete original horizontal coordinate. -/
@[simp] theorem coefficientRingMapTo_x :
    coefficientRingMapTo f W s b3 b4 b6 U t c3 c4 c6 hW hs h3 h4 h6
      (x W s b3 b4 b6) = x U t c3 c4 c6 := by
  subst U t c3 c4 c6
  exact coefficientRingMap_x f W s b3 b4 b6

/-- Explicit transport retains the complete original vertical coordinate. -/
@[simp] theorem coefficientRingMapTo_y :
    coefficientRingMapTo f W s b3 b4 b6 U t c3 c4 c6 hW hs h3 h4 h6
      (y W s b3 b4 b6) = y U t c3 c4 c6 := by
  subst U t c3 c4 c6
  exact coefficientRingMap_y f W s b3 b4 b6

/-- Explicit target transport uses exactly the original coefficient homomorphism. -/
@[simp] theorem coefficientRingMapTo_algebraMap (a : R) :
    coefficientRingMapTo f W s b3 b4 b6 U t c3 c4 c6 hW hs h3 h4 h6
      (algebraMap R _ a) = algebraMap S _ (f a) := by
  subst U t c3 c4 c6
  exact coefficientRingMap_algebraMap f W s b3 b4 b6 a

end FLT.Mazur.WeierstrassDilatation
