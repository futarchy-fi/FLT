/-
Copyright (c) 2026 krandder. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: krandder
-/
module

public import FLT.Mazur.WeierstrassIntegralProjectiveClosed
public import FLT.Mazur.WeierstrassIntegralFaithfullyFlat
public import FLT.Mazur.ProjectiveSpaceProper

/-!
# Properness of the actual integral Weierstrass cubic

The constructed closed immersion into projective two-space proves properness
of the original glued structure morphism. The zero section makes every base
change a closed surjection, including the singular fibers.
-/

@[expose] public noncomputable section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits

namespace FLT.Mazur.WeierstrassIntegralChart

set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
attribute [local instance] MvPolynomial.gradedAlgebra

universe u
variable {R : Type u} [CommRing R] (W : WeierstrassCurve R)

/-- The actual integral cubic is proper over every commutative coefficient ring. -/
instance integralCurveStructure_proper : IsProper (integralCurveStructure W) := by
  rw [← integralProjectiveMap_baseProjection]
  infer_instance

/-- Properness makes the original structure map closed. -/
theorem integralCurveStructure_isClosedMap : IsClosedMap (integralCurveStructure W) :=
  (integralCurveStructure W).isClosedMap

variable {S : Scheme.{u}} (f : S ⟶ Spec (.of R))

/-- Properness persists after arbitrary scheme base change. -/
instance integralCurveBaseChange_proper :
    IsProper (pullback.snd (integralCurveStructure W) f) := inferInstance

/-- Every base change is a closed surjection, including at primes of bad reduction. -/
theorem integralCurveBaseChange_closedSurjective :
    IsClosedMap (pullback.snd (integralCurveStructure W) f) ∧
      Function.Surjective (pullback.snd (integralCurveStructure W) f) :=
  ⟨(pullback.snd (integralCurveStructure W) f).isClosedMap,
    (pullback.snd (integralCurveStructure W) f).surjective⟩

end FLT.Mazur.WeierstrassIntegralChart
