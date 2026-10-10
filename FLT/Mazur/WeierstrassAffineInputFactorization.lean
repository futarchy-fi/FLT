/-
Copyright (c) 2026 krandder. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: krandder
-/
module

public import FLT.Mazur.WeierstrassChartFactorUnit
public import FLT.Mazur.WeierstrassAffineOutputDomains

/-!
# Affine input projections and forced ordinary replacements

Every affine-input law retains both input coordinates in the affine chart.
If its actual sum also has an affine presentation, the overlap supplies the
output unit and hence an ordinary replacement with exactly the same inputs.
-/

@[expose] public noncomputable section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits

namespace FLT.Mazur.WeierstrassIntegralChart

set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true

universe u
variable {R : Type u} [CommRing R] (W : WeierstrassCurve R) {X : Scheme.{u}}

/-- The first affine input of any ordinary or reciprocal domain. -/
def additionAffineInputLeft (i : AdditionChartIndex) :
    Spec (additionChartRing W i) ⟶ chartScheme W 2 :=
  additionChartInclusion W i ≫ Spec.map (CommRingCat.ofHom (productLeft W).toRingHom)

/-- The second affine input of any ordinary or reciprocal domain. -/
def additionAffineInputRight (i : AdditionChartIndex) :
    Spec (additionChartRing W i) ⟶ chartScheme W 2 :=
  additionChartInclusion W i ≫ Spec.map (CommRingCat.ofHom (productRight W).toRingHom)

/-- The first projection is the original affine input, viewed in the global curve. -/
@[reassoc] theorem additionGlobalDomain_fst (i : AdditionChartIndex) :
    additionGlobalDomain W i ≫ pullback.fst _ _ =
      additionAffineInputLeft W i ≫ integralCurveChart W 2 := by
  rw [additionGlobalDomain, Category.assoc, integralCurveProductChart_fst]
  rfl

/-- The second projection is the original affine input, viewed in the global curve. -/
@[reassoc] theorem additionGlobalDomain_snd (i : AdditionChartIndex) :
    additionGlobalDomain W i ≫ pullback.snd _ _ =
      additionAffineInputRight W i ≫ integralCurveChart W 2 := by
  rw [additionGlobalDomain, Category.assoc, integralCurveProductChart_snd]
  rfl

/-- Each of the four domains retains its actual normalized output. -/
@[reassoc] theorem additionGlobalDomain_addition (hΔ : IsUnit W.Δ)
    (i : AdditionChartIndex) :
    additionGlobalDomain W i ≫ integralCurveAddition W hΔ =
      Spec.map (CommRingCat.ofHom (additionChartAlgOutput W i).toRingHom) ≫
        integralCurveChart W (additionChartOutput i) := by
  rw [additionGlobalDomain, Category.assoc, integralCurveProductChart_affine_addition,
    additionCurveChart_glued, additionCurveChart, additionChartAlgOutput_spec]

/-- An affine presentation forces the normalized output z-coordinate to be a unit. -/
theorem additionOutput_isUnit_of_affine (hΔ : IsUnit W.Δ) (i : AdditionChartIndex)
    (f : X ⟶ Spec (additionChartRing W i)) (g : X ⟶ chartScheme W 2)
    (h : f ≫ additionGlobalDomain W i ≫ integralCurveAddition W hΔ =
      g ≫ integralCurveChart W 2) :
    IsUnit (specSectionHom f
      (additionChartAlgOutput W i (coord W (additionChartOutput i) 2))) := by
  rw [additionGlobalDomain_addition] at h
  have hu := chartCoordinate_isUnit_of_global_eq W (additionChartOutput i) 2
    (f ≫ Spec.map (CommRingCat.ofHom (additionChartAlgOutput W i).toRingHom)) g
    ((Category.assoc _ _ _).trans h)
  rw [specSectionHom_comp] at hu
  exact hu

/-- Every affine-valued affine-input law has an ordinary replacement preserving its pair. -/
theorem exists_ordinary_of_addition_affine (hΔ : IsUnit W.Δ) (i : AdditionChartIndex)
    (f : X ⟶ Spec (additionChartRing W i)) (g : X ⟶ chartScheme W 2)
    (h : f ≫ additionGlobalDomain W i ≫ integralCurveAddition W hΔ =
      g ≫ integralCurveChart W 2) :
    ∃ f' : X ⟶ Spec (additionChartRing W (ordinaryIndex (additionOrdinaryChoice i))),
      f' ≫ ordinaryGlobalDomain W (additionOrdinaryChoice i) = f ≫ additionGlobalDomain W i := by
  let hz := additionOutput_isUnit_of_affine W hΔ i f g h
  exact ⟨additionAffineOutputScheme W i f hz, additionAffineOutputScheme_inputs W i f hz⟩

end FLT.Mazur.WeierstrassIntegralChart
