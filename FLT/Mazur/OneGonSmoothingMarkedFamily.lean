/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.OneGonSmoothingMarkingAmple
public import FLT.Mazur.WeierstrassSmoothZeroSection

/-!
# The complete one-gon family with its actual smooth ample marking

The explicit infinity point is smooth even on the singular closed fiber.
Together with the actual divisor line and the constructed genus-one family,
this supplies the complete marked contract without any assumed geometric fields.
-/

@[expose] public noncomputable section
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
namespace FLT.Mazur.OneGonSmoothing
open FCurve WeierstrassIntegralChart
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
universe u
variable {R : Type u} [CommRing R] (t : R)

/-- The actual infinity marking lies in the relative smooth locus for every parameter. -/
theorem marking_range_smoothLocus :
    let _ := family_lfp t
    Set.range (marking t) ⊆ ((family t).hom.smoothLocus : Set (family t).left) :=
  integralCurveZero_range_smooth (equation t)

variable (K : Type) [Field K]

/-- The constructed complete smoothing retains all actual smooth ample marked-family data. -/
theorem complete_markedFamily :
    let t := (PowerSeries.X : PowerSeries K)
    let _ := family_lfp t
    ClassifiedGenusOneFamily (family t).hom ∧
      marking t ≫ (family t).hom = 𝟙 _ ∧
      Set.range (marking t) ⊆ ((family t).hom.smoothLocus : Set (family t).left) ∧
      RelativeEffectiveCartier (family t).hom (marking t).ker ∧
      LocallyFreeRankOne (markingLine t) ∧
      RelativelyAmpleLineBundle (family t).hom (markingLine t) :=
  ⟨complete_classifiedGenusOneFamily K, marking_toBase _, marking_range_smoothLocus _,
    marking_relativeCartier _, markingLine_rankOne _, completeMarkingLine_relativelyAmple K⟩

/-- The actual original identity marking is retained on the complete closed-fiber square. -/
@[reassoc] theorem original_marking_closedFiber (i : Fin 1) :
    PolygonMarkedSections.sectionMap K 1 (OneGonNormalization.normalizationOver K) 1 i ≫
      (powerSeriesClosedFiberIso K).hom =
        fiberMarking (PowerSeries.X : PowerSeries K)
          (Spec.map (CommRingCat.ofHom (PowerSeries.constantCoeff (R := K)))) := by
  let _ : Algebra (PowerSeries K) K := (PowerSeries.constantCoeff (R := K)).toAlgebra
  apply pullback.hom_ext
  · rw [Category.assoc, fiberMarking_fst]
    exact zeroParameterFiberIso_marking_fst K PowerSeries.X PowerSeries.constantCoeff_X i
  · rw [Category.assoc, powerSeriesClosedFiberIso_snd, fiberMarking_snd]
    exact PolygonMarkedSections.section_base K 1 _ 1 i

end FLT.Mazur.OneGonSmoothing
