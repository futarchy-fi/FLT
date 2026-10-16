/-
Copyright (c) 2026 krandder. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: krandder
-/
module

public import FLT.Mazur.WeierstrassModificationXCoefficientRingMap

/-!
# Explicit coefficient transport of the entire initial equation

Naming equal target coefficients avoids reducing quotient maps inside large
node constructions. The map still preserves every original coordinate.
-/

@[expose] public noncomputable section
namespace FLT.Mazur.WeierstrassModificationX
variable {R S : Type*} [CommRing R] [CommRing S] (f : R →+* S)
  (W : WeierstrassCurve R) (s b3 b4 b6 : R)
  (U : WeierstrassCurve S) (s' c3 c4 c6 : S)
  (hW : W.map f = U) (hs : f s = s') (h3 : f b3 = c3)
  (h4 : f b4 = c4) (h6 : f b6 = c6)

/-- The original coefficient map with explicitly identified target coefficients. -/
def coefficientRingMapTo : Coordinate W s b3 b4 b6 →+* Coordinate U s' c3 c4 c6 := by
  subst U s' c3 c4 c6
  exact coefficientRingMap f W s b3 b4 b6

/-- Explicit transport retains the complete original incidence coordinate. -/
@[simp] theorem coefficientRingMapTo_t :
    coefficientRingMapTo f W s b3 b4 b6 U s' c3 c4 c6 hW hs h3 h4 h6
      (t W s b3 b4 b6) = t U s' c3 c4 c6 := by
  subst U s' c3 c4 c6
  exact coefficientRingMap_t f W s b3 b4 b6

/-- Explicit transport retains the complete original slope coordinate. -/
@[simp] theorem coefficientRingMapTo_v :
    coefficientRingMapTo f W s b3 b4 b6 U s' c3 c4 c6 hW hs h3 h4 h6
      (v W s b3 b4 b6) = v U s' c3 c4 c6 := by
  subst U s' c3 c4 c6
  exact coefficientRingMap_v f W s b3 b4 b6

/-- Explicit target transport uses exactly the original coefficient homomorphism. -/
@[simp] theorem coefficientRingMapTo_algebraMap (a : R) :
    coefficientRingMapTo f W s b3 b4 b6 U s' c3 c4 c6 hW hs h3 h4 h6
      (algebraMap R _ a) = algebraMap S _ (f a) := by
  subst U s' c3 c4 c6
  exact coefficientRingMap_scalar f W s b3 b4 b6 a

end FLT.Mazur.WeierstrassModificationX
