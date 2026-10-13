/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.OddWeierstrassSpecializationGroup
public import FLT.Mazur.OddWeierstrassAuxiliaryEtale
public import FLT.Mazur.AuxiliaryCartesianGroupParameter

/-!
# Actual etale auxiliary covers of original smooth cubics

Pull back the established universal auxiliary cover along the original five
coefficients. Transport its full marking through the actual coefficient group
comparison, producing a faithful parameter on the original cubic over every ring
with three and the discriminant invertible, including nonreduced rings.
-/

@[expose] public noncomputable section
open CategoryTheory Limits AlgebraicGeometry
namespace FLT.Mazur.OddWeierstrassParameter
open WeierstrassIntegralChart AuxiliaryLevel
open IntegralWeierstrassParameter (oddChartEquation oddChart_discriminant)
open UniversalWeierstrass (Labels)
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
variable {R : Type} [CommRing R] (W : WeierstrassCurve R)
  (h₃ : IsUnit (3 : R)) (hΔ : IsUnit W.Δ)

/-- The actual auxiliary cover pulled back along the original coefficient map. -/
def originalAuxiliaryCover : Over (Spec (.of R)) :=
  (Over.pullback (specializationBase W h₃ hΔ)).obj levelThree

/-- The actual cover is etale, including over nonreduced coefficient rings. -/
instance originalAuxiliaryCover_etale : Etale (originalAuxiliaryCover W h₃ hΔ).hom :=
  inferInstanceAs (Etale (pullback.snd levelThree.hom (specializationBase W h₃ hΔ)))

/-- Every original coefficient point is covered. -/
instance originalAuxiliaryCover_surjective : Surjective (originalAuxiliaryCover W h₃ hΔ).hom :=
  inferInstanceAs (Surjective (pullback.snd levelThree.hom (specializationBase W h₃ hΔ)))

/-- The projection is an actual original universal auxiliary parameter. -/
def originalAuxiliaryCoverProjection :
    (Over.map (specializationBase W h₃ hΔ)).obj (originalAuxiliaryCover W h₃ hΔ) ⟶
      levelThree :=
  Over.homMk (pullback.fst levelThree.hom (specializationBase W h₃ hΔ)) pullback.condition

/-- Its complete marking is an actual faithful parameter for the original cubic group. -/
def originalAuxiliaryParameter : originalAuxiliaryCover W h₃ hΔ ⟶
    faithfulScheme (integralCurveGroup W hΔ).X (Labels 3) :=
  cartesianGroupParameter (specializationBase W h₃ hΔ)
    (integralCurveGroup oddChartEquation oddChart_discriminant)
    (integralCurveGroup W hΔ) (specializationGroupIso W h₃ hΔ).symm (Labels 3)
    (originalAuxiliaryCoverProjection W h₃ hΔ)

include h₃ in
/-- Original smooth cubics admit full faithful auxiliary markings on an actual etale cover. -/
theorem exists_original_auxiliary_cover :
    ∃ (U : Scheme) (g : U ⟶ Spec (.of R)), Etale g ∧ Surjective g ∧
      Nonempty (Over.mk g ⟶ faithfulScheme (integralCurveGroup W hΔ).X (Labels 3)) :=
  ⟨(originalAuxiliaryCover W h₃ hΔ).left, (originalAuxiliaryCover W h₃ hΔ).hom,
    inferInstance, inferInstance, ⟨originalAuxiliaryParameter W h₃ hΔ⟩⟩

end FLT.Mazur.OddWeierstrassParameter
