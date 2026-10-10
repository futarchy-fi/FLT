/-
Copyright (c) 2026 krandder. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: krandder
-/
module

public import FLT.Mazur.WeierstrassModificationXExtendedCastEvaluation
/-!
# Extended coefficients followed by the full normal-form comparison

This comparison composes the proved coefficient casts with the original
normal-form equivalence. Both generators are evaluated at this compiled
boundary, with the constant coefficient retained.
-/

@[expose] public noncomputable section

namespace FLT.Mazur.WeierstrassModificationX
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
variable {R S : Type*} [CommRing R] [CommRing S] [Algebra R S]
  (W : WeierstrassCurve R) (s b3 b4 b6 : R) (a : S)
  (hs : algebraMap R S s = 0) (h3 : algebraMap R S b3 = 0)
  (h4 : algebraMap R S b4 = 0)
  (h1 : (W.map (algebraMap R S)).a₁ = a)
  (h2 : (W.map (algebraMap R S)).a₂ = 0)
/-- The full normal form after vanishing of the three linear coefficients. -/
def extendedNormalEquiv : ExtendedCoordinate W s b3 b4 b6 S ≃ₐ[S]
    FiberCoordinate a (algebraMap R S b6) :=
  zeroExtendedCoefficientsEquiv W s b3 b4 b6 hs h3 h4
    (fiberNormalEquiv a (algebraMap R S b6) (W.map (algebraMap R S)) h1 h2)
/-- The extended normal comparison preserves the incidence coordinate. -/
theorem extendedNormalEquiv_t : extendedNormalEquiv W s b3 b4 b6 a hs h3 h4 h1 h2
    (t (W.map (algebraMap R S)) (algebraMap R S s)
      (algebraMap R S b3) (algebraMap R S b4) (algebraMap R S b6)) =
    fiberT a (algebraMap R S b6) := by
  rw [extendedNormalEquiv, zeroExtendedCoefficientsEquiv_t, fiberNormalEquiv_t]
/-- The extended normal comparison preserves the tangent slope. -/
theorem extendedNormalEquiv_v : extendedNormalEquiv W s b3 b4 b6 a hs h3 h4 h1 h2
    (v (W.map (algebraMap R S)) (algebraMap R S s)
      (algebraMap R S b3) (algebraMap R S b4) (algebraMap R S b6)) =
    fiberV a (algebraMap R S b6) := by
  rw [extendedNormalEquiv, zeroExtendedCoefficientsEquiv_v, fiberNormalEquiv_v]
end FLT.Mazur.WeierstrassModificationX
