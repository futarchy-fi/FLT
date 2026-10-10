/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.WeierstrassCoefficientGroup
public import FLT.Mazur.GroupMarkingBaseChange
public import FLT.Mazur.GroupMarkingTransport

/-!
# Complete group markings on the actual coefficient-extended cubic

The actual pullback adjunction and proved group comparison transport the whole
label homomorphism. Injectivity is preserved and reflected on every test scheme.
-/

@[expose] public noncomputable section

open WeierstrassCurve CategoryTheory CategoryTheory.Limits AlgebraicGeometry MonoidalCategory MonObj

namespace FLT.Mazur.WeierstrassIntegralChart

attribute [local irreducible] integralCurveGroup integralCurveCoefficientGroupIso

set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false

universe u
variable {R S : Type u} [CommRing R] [CommRing S] [Algebra R S]
  (W : WeierstrassCurve R)

local notation "V" => W.map (algebraMap R S)

local notation "F" => Over.pullback (Spec.map (CommRingCat.ofHom (algebraMap R S)))

variable (hW : IsUnit W.Δ) (hV : IsUnit (W.map (algebraMap R S)).Δ)
  {L : Type*} [Monoid L] (T : Over (Spec (.of S)))

/-- Transport the full marking into the original coefficient-extended cubic. -/
def integralCoefficientMarking
    (m : L →* ((Over.map (Spec.map (CommRingCat.ofHom (algebraMap R S)))).obj T ⟶
      (integralCurveGroup W hW).X)) : L →* (T ⟶ (integralCurveGroup V hV).X) :=
  GroupMarkingTransport.transport
    ((F).mapCommGrp.obj (integralCurveGroup W hW)) (integralCurveGroup V hV)
    (integralCurveCoefficientGroupIso W hW hV).symm
    (GroupMarkingBaseChange.marking _ (integralCurveGroup W hW).X T m)

/-- The full original marking is faithful exactly when its coefficient transport is faithful. -/
theorem integralCoefficientMarking_injective_iff
    (m : L →* ((Over.map (Spec.map (CommRingCat.ofHom (algebraMap R S)))).obj T ⟶
      (integralCurveGroup W hW).X)) :
    Function.Injective (integralCoefficientMarking W hW hV T m) ↔ Function.Injective m := by
  unfold integralCoefficientMarking
  rw [GroupMarkingTransport.transport_injective_iff]
  exact GroupMarkingBaseChange.marking_injective_iff _ _ T m

end FLT.Mazur.WeierstrassIntegralChart
