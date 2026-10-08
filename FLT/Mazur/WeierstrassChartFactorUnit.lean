/-
Copyright (c) 2026 krandder. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: krandder
-/
module

public import FLT.Mazur.WeierstrassIntegralProductOverlap
public import FLT.Mazur.WeierstrassOrdinarySchemeLift
public import FLT.Mazur.WeierstrassOrdinaryGlobalDomains
public import FLT.Mazur.WeierstrassReciprocalGlobalDomains

/-!
# Units forced by a second chart presentation

Two chart presentations of the same curve-valued morphism factor through the
actual overlap. Its inverted coordinate is therefore a unit on global sections.
This derives the unit needed to replace an affine-valued reciprocal addition.
-/

@[expose] public noncomputable section

open AlgebraicGeometry CategoryTheory

namespace FLT.Mazur.WeierstrassIntegralChart

set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true

universe u
variable {R : Type u} [CommRing R] (W : WeierstrassCurve R) {X : Scheme.{u}}

/-- A second presentation forces the actual overlap coordinate to be invertible. -/
theorem chartCoordinate_isUnit_of_global_eq (j k : Fin 3)
    (f : X ⟶ chartScheme W j) (g : X ⟶ chartScheme W k)
    (h : f ≫ integralCurveChart W j = g ≫ integralCurveChart W k) :
    IsUnit (specSectionHom f (coord W j k)) := by
  obtain ⟨v, hv, _⟩ := (integralCurveChart_overlap_isPullback W j k).exists_lift f g h
  rw [← hv, ← overlapRestriction_spec, specSectionHom_comp]
  exact (overlapCoord_isUnit W j k).map (specSectionHom v)

/-- An actual affine presentation of a reciprocal output supplies its missing unit. -/
theorem reciprocalOutput_isUnit_of_affine (hΔ : IsUnit W.Δ) (b : Bool)
    (f : X ⟶ Spec (additionChartRing W (reciprocalIndex b)))
    (g : X ⟶ chartScheme W 2)
    (h : f ≫ reciprocalGlobalDomain W b ≫ integralCurveAddition W hΔ =
      g ≫ integralCurveChart W 2) :
    IsUnit (specSectionHom f (reciprocalChartAddition W b (coord W 1 2))) := by
  rw [reciprocalGlobalDomain_addition] at h
  have hu := chartCoordinate_isUnit_of_global_eq W 1 2
    (f ≫ Spec.map (CommRingCat.ofHom (reciprocalChartAddition W b).toRingHom)) g
    ((Category.assoc _ _ _).trans h)
  rw [specSectionHom_comp] at hu
  exact hu

/-- Replacing an affine-valued reciprocal law preserves the full global input pair. -/
theorem reciprocalAffineOrdinaryScheme_globalInputs (b : Bool)
    (f : X ⟶ Spec (additionChartRing W (reciprocalIndex b)))
    (hz : IsUnit (specSectionHom f (reciprocalChartAddition W b (coord W 1 2)))) :
    reciprocalAffineOrdinaryScheme W b f hz ≫ ordinaryGlobalDomain W b =
      f ≫ reciprocalGlobalDomain W b := by
  change reciprocalAffineOrdinaryScheme W b f hz ≫
    additionChartInclusion W (ordinaryIndex b) ≫ _ = _
  rw [← Category.assoc, reciprocalAffineOrdinaryScheme_inputs, Category.assoc]
  rfl

/-- An affine presentation yields an ordinary replacement with the original inputs. -/
theorem exists_ordinary_of_reciprocal_affine (hΔ : IsUnit W.Δ) (b : Bool)
    (f : X ⟶ Spec (additionChartRing W (reciprocalIndex b)))
    (g : X ⟶ chartScheme W 2)
    (h : f ≫ reciprocalGlobalDomain W b ≫ integralCurveAddition W hΔ =
      g ≫ integralCurveChart W 2) :
    ∃ f' : X ⟶ Spec (additionChartRing W (ordinaryIndex b)),
      f' ≫ ordinaryGlobalDomain W b = f ≫ reciprocalGlobalDomain W b := by
  let hz := reciprocalOutput_isUnit_of_affine W hΔ b f g h
  exact ⟨reciprocalAffineOrdinaryScheme W b f hz,
    reciprocalAffineOrdinaryScheme_globalInputs W b f hz⟩

end FLT.Mazur.WeierstrassIntegralChart
