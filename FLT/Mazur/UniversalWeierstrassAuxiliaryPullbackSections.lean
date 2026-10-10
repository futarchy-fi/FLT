/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.UniversalWeierstrassAuxiliaryCoordinateSections
public import FLT.Mazur.WeierstrassChartEvaluationComparison

/-!
# Actual auxiliary sections after an arbitrary ring pullback

The original global coordinate functions evaluate in every ring receiving the
auxiliary section ring. They give sections of the original integral cubic of
the pulled-back equation, with their coefficient map and coordinates retained.
-/

@[expose] public noncomputable section

open CategoryTheory AlgebraicGeometry

namespace FLT.Mazur.UniversalWeierstrass

open WeierstrassIntegralChart

set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false

variable {R : Type} [CommRing R] (g : AuxiliarySectionRing →+* R)

/-- The original smooth equation after pulling back auxiliary global functions. -/
def auxiliaryPullbackEquation : WeierstrassCurve R := auxiliarySectionEquation.map g

/-- Smoothness survives every such ring pullback. -/
theorem auxiliaryPullbackEquation_discriminant : IsUnit (auxiliaryPullbackEquation g).Δ := by
  rw [auxiliaryPullbackEquation, auxiliarySectionEquation, WeierstrassCurve.map_Δ,
    WeierstrassCurve.map_Δ]
  exact (smoothEquation_discriminant.map auxiliaryCoefficientSections).map g

/-- The original marked coordinates satisfy the actual pulled-back homogeneous equation. -/
theorem auxiliaryPullbackCoordinate_equation (a : Labels 4) (ha : a ≠ 1) :
    (auxiliaryPullbackEquation g).toProjective.Equation
      (fun i ↦ g (auxiliaryCoordinate a ha i)) := by
  have h := (coord_equation smoothEquation 2).map
    (g.comp (auxiliaryCoordinateSections a ha))
  have he : (smoothEquation.map (algebraMap ParameterRing
      (Coordinate smoothEquation 2))).map (g.comp (auxiliaryCoordinateSections a ha)) =
        auxiliaryPullbackEquation g := by
    ext <;> exact congrArg g (auxiliaryCoordinateSections_coeff a ha _)
  change ((smoothEquation.map _).map _).toProjective.Equation _ at h
  rw [he] at h
  exact h

/-- The original normalized coordinate remains one after pullback. -/
theorem auxiliaryPullbackCoordinate_z (a : Labels 4) (ha : a ≠ 1) :
    g (auxiliaryCoordinate a ha 2) = 1 := by
  rw [auxiliaryCoordinate, coord_self, map_one, map_one]

/-- Evaluation on the new coefficient algebra retains all original marked coordinates. -/
def auxiliaryPullbackEvaluation (a : Labels 4) (ha : a ≠ 1) :
    Coordinate (auxiliaryPullbackEquation g) 2 →ₐ[R] R :=
  evaluation _ 2 (fun i ↦ g (auxiliaryCoordinate a ha i))
    (by simpa only [Algebra.algebraMap_self, WeierstrassCurve.map_id] using
      auxiliaryPullbackCoordinate_equation g a ha)
    (auxiliaryPullbackCoordinate_z g a ha)

/-- Evaluation gives exactly the original global coordinate after ring pullback. -/
@[simp] theorem auxiliaryPullbackEvaluation_coord (a : Labels 4) (ha : a ≠ 1) (i : Fin 3) :
    auxiliaryPullbackEvaluation g a ha (coord (auxiliaryPullbackEquation g) 2 i) =
      g (auxiliaryCoordinate a ha i) := evaluation_coord _ _ _ _ _ _

/-- The marked point is an actual morphism into the original pulled-back cubic. -/
def auxiliaryPullbackSection (a : Labels 4) (ha : a ≠ 1) :
    Spec (.of R) ⟶ integralCurve (auxiliaryPullbackEquation g) :=
  Spec.map (CommRingCat.ofHom (auxiliaryPullbackEvaluation g a ha).toRingHom) ≫
    integralCurveChart (auxiliaryPullbackEquation g) 2

/-- The marked point is a section over the entire coefficient ring. -/
theorem auxiliaryPullbackSection_structure (a : Labels 4) (ha : a ≠ 1) :
    auxiliaryPullbackSection g a ha ≫ integralCurveStructure (auxiliaryPullbackEquation g) =
      𝟙 _ := by
  rw [auxiliaryPullbackSection, Category.assoc, integralCurveChart_structure,
    chartStructure, specAlgHom_structure]
  exact Spec.map_id _

end FLT.Mazur.UniversalWeierstrass
