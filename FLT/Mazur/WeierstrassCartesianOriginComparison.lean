/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.WeierstrassCoefficientGroup
public import FLT.Mazur.WeierstrassOriginIsomorphismGroup

/-!
# Comparing a chosen pointed cartesian cubic with coefficient extension

A cartesian morphism preserving infinity identifies the independently chosen
cubic with the coefficient extension. The actual comparison preserves the
constructed group laws; no equality of the two chosen equations is needed.
-/

@[expose] public noncomputable section
open CategoryTheory AlgebraicGeometry
namespace FLT.Mazur.WeierstrassIntegralChart
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
variable {R S : Type} [CommRing R] [CommRing S] [Algebra R S]
  (W : WeierstrassCurve R) (V : WeierstrassCurve S)
  (f : integralCurve V ⟶ integralCurve W)
  (hf : IsPullback f (integralCurveStructure V) (integralCurveStructure W)
    (Spec.map (CommRingCat.ofHom (algebraMap R S))))
  (hz : integralCurveZero V ≫ f =
    Spec.map (CommRingCat.ofHom (algebraMap R S)) ≫ integralCurveZero W)
local notation "U" => W.map (algebraMap R S)

/-- The specified cartesian square gives the actual comparison of the two cubics. -/
def cartesianCoefficientIso : integralCurve U ≅ integralCurve V :=
  (integralCoefficient_isPullback W).isoIsPullback _ _ hf

/-- The comparison lies over the extended coefficient ring. -/
@[reassoc] theorem cartesianCoefficientIso_over :
    (cartesianCoefficientIso W V f hf).hom ≫ integralCurveStructure V =
      integralCurveStructure U :=
  (integralCoefficient_isPullback W).isoIsPullback_hom_snd _ _ hf

/-- The comparison retains the original coefficient morphism. -/
@[reassoc] theorem cartesianCoefficientIso_map :
    (cartesianCoefficientIso W V f hf).hom ≫ f = integralCoefficientMorphism W :=
  (integralCoefficient_isPullback W).isoIsPullback_hom_fst _ _ hf

include hz in
/-- Cartesian uniqueness makes the comparison preserve the chosen infinity. -/
@[reassoc] theorem cartesianCoefficientIso_zero :
    integralCurveZero U ≫ (cartesianCoefficientIso W V f hf).hom =
      integralCurveZero V := by
  apply hf.hom_ext
  · rw [Category.assoc, cartesianCoefficientIso_map, integralCoefficientMorphism_zero, hz]
  · rw [Category.assoc, cartesianCoefficientIso_over, integralCurveZero_structure,
      integralCurveZero_structure]

/-- The actual pointed comparison preserves the independently constructed group laws. -/
irreducible_def cartesianCoefficientGroupIso (hU : IsUnit (U).Δ) (hV : IsUnit V.Δ) :
    integralCurveGroup U hU ≅ integralCurveGroup V hV :=
  originIsoGroupIso U V hU hV (cartesianCoefficientIso W V f hf)
    (cartesianCoefficientIso_over W V f hf) (cartesianCoefficientIso_zero W V f hf hz)

/-- Forgetting the group upgrade returns the original cartesian comparison. -/
theorem cartesianCoefficientGroupIso_hom (hU : IsUnit (U).Δ) (hV : IsUnit V.Δ) :
    (cartesianCoefficientGroupIso W V f hf hz hU hV).hom.hom.hom.hom.left =
      (cartesianCoefficientIso W V f hf).hom := by
  rw [cartesianCoefficientGroupIso_def]
  rfl

end FLT.Mazur.WeierstrassIntegralChart
