/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.WeierstrassSpecializationGroup
public import FLT.Mazur.UniversalWeierstrassAuxiliaryEtale
public import FLT.Mazur.AuxiliaryCartesianGroupParameter

/-!
# Actual etale auxiliary covers of original smooth cubics

Pull back the established universal auxiliary cover along the original five
coefficients. Transport its full marking through the actual coefficient group
comparison, producing a faithful parameter on the original cubic over every ring
with two and the discriminant invertible, including nonreduced rings.
-/

@[expose] public noncomputable section
open CategoryTheory Limits AlgebraicGeometry
namespace FLT.Mazur.UniversalWeierstrass
open WeierstrassIntegralChart AuxiliaryLevel
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
variable {R : Type} [CommRing R] (W : WeierstrassCurve R)
  (h₂ : IsUnit (2 : R)) (hΔ : IsUnit W.Δ)

/-- The actual auxiliary cover pulled back along the original coefficient map. -/
def originalAuxiliaryCover : Over (Spec (.of R)) :=
  (Over.pullback (specializationBase W h₂ hΔ)).obj levelFour

/-- The actual cover is etale, including over nonreduced coefficient rings. -/
instance originalAuxiliaryCover_etale : Etale (originalAuxiliaryCover W h₂ hΔ).hom :=
  inferInstanceAs (Etale (pullback.snd levelFour.hom (specializationBase W h₂ hΔ)))

/-- Every original coefficient point is covered. -/
instance originalAuxiliaryCover_surjective : Surjective (originalAuxiliaryCover W h₂ hΔ).hom :=
  inferInstanceAs (Surjective (pullback.snd levelFour.hom (specializationBase W h₂ hΔ)))

/-- The projection is an actual original universal auxiliary parameter. -/
def originalAuxiliaryCoverProjection :
    (Over.map (specializationBase W h₂ hΔ)).obj (originalAuxiliaryCover W h₂ hΔ) ⟶
      levelFour :=
  Over.homMk (pullback.fst levelFour.hom (specializationBase W h₂ hΔ)) pullback.condition

/-- Its complete marking is an actual faithful parameter for the original cubic group. -/
def originalAuxiliaryParameter : originalAuxiliaryCover W h₂ hΔ ⟶
    faithfulScheme (integralCurveGroup W hΔ).X (Labels 4) :=
  cartesianGroupParameter (specializationBase W h₂ hΔ)
    (integralCurveGroup smoothEquation smoothEquation_discriminant)
    (integralCurveGroup W hΔ) (specializationGroupIso W h₂ hΔ).symm (Labels 4)
    (originalAuxiliaryCoverProjection W h₂ hΔ)

include h₂ in
/-- Original smooth cubics admit full faithful auxiliary markings on an actual etale cover. -/
theorem exists_original_auxiliary_cover :
    ∃ (U : Scheme) (g : U ⟶ Spec (.of R)), Etale g ∧ Surjective g ∧
      Nonempty (Over.mk g ⟶ faithfulScheme (integralCurveGroup W hΔ).X (Labels 4)) :=
  ⟨(originalAuxiliaryCover W h₂ hΔ).left, (originalAuxiliaryCover W h₂ hΔ).hom,
    inferInstance, inferInstance, ⟨originalAuxiliaryParameter W h₂ hΔ⟩⟩

end FLT.Mazur.UniversalWeierstrass
