/-
Copyright (c) 2026 krandder. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: krandder
-/
module

public import FLT.FreyCurve.Serre.VeluGlobalKernelIdentityOpen

/-!
# Simple fibers at the original translated kernel points

The original inverse translations carry the simple infinity neighborhood
to simple neighborhoods of the negative translating points.
-/

@[expose] public noncomputable section

open CategoryTheory AlgebraicGeometry FLT.Mazur.WeierstrassIntegralChart

namespace WeierstrassCurve.Velu

set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true

variable {K : Type} [Field K] [CharZero K] [DecidableEq K]
  (E : WeierstrassCurve K) (G : AddSubgroup E.toAffine.Point) [Fintype G]

/-- The simple source neighborhood transported by original inverse translation. -/
def veluTranslatedSimpleOpenImmersion (P : E.toAffine.Point) :
    Spec (.of (InfinitySimpleRing E G)) ⟶ integralCurve E :=
  veluSimpleRestriction E G ≫ veluTranslatedInfinityOpenImmersion E G P

/-- The transported simple neighborhood is open in the original cubic. -/
instance veluTranslatedSimpleOpenImmersion_isOpenImmersion (P : E.toAffine.Point) :
    IsOpenImmersion (veluTranslatedSimpleOpenImmersion E G P) :=
  inferInstanceAs (IsOpenImmersion
    (veluSimpleRestriction E G ≫ veluTranslatedInfinityOpenImmersion E G P))

/-- The lifted identity becomes the original negative translating point. -/
@[reassoc] theorem veluTranslatedSimplePoint_source (P : E.toAffine.Point) :
    veluSimplePointLift E G ≫ veluTranslatedSimpleOpenImmersion E G P =
      affineSmoothPoint E (-P) ≫ (integralSmoothOpen E).ι := by
  rw [veluTranslatedSimpleOpenImmersion, veluSimplePointLift_restriction_assoc,
    veluTranslatedInfinityPoint_source]

variable [IsAlgClosed K] [E.IsElliptic] (hodd : ∀ Q : G, Q ≠ 0 → Q ≠ -Q)

/-- The actual global map on a translated simple neighborhood is the original local map. -/
@[reassoc] theorem veluGlobalMorphism_translatedSimple {u v : K}
    (hQ : E.toAffine.Nonsingular u v) (hQG : Affine.Point.some u v hQ ∈ G) :
    veluTranslatedSimpleOpenImmersion E G (.some u v hQ) ≫
        veluGlobalMorphism E G hodd = veluSimpleRegularMorphism E G hodd := by
  rw [veluTranslatedSimpleOpenImmersion, Category.assoc,
    veluGlobalMorphism_translatedInfinity E G hodd hQ hQG,
    veluSimpleRegularMorphism_restriction]

/-- The entire fiber on the translated source open is the original field point. -/
theorem veluTranslatedSimple_identityFiber {u v : K}
    (hQ : E.toAffine.Nonsingular u v) (hQG : Affine.Point.some u v hQ ∈ G) :
    IsPullback (veluSimplePointLift E G) (𝟙 (Spec (.of K)))
      (veluTranslatedSimpleOpenImmersion E G (.some u v hQ) ≫
        veluGlobalMorphism E G hodd) (integralCurveZero (curve E G)) := by
  rw [veluGlobalMorphism_translatedSimple E G hodd hQ hQG]
  exact veluSimpleRegularMorphism_identityFiber E G hodd

end WeierstrassCurve.Velu
