/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.OneGonSmoothingNormalizedOverlap
public import FLT.Mazur.OneGonSmoothingPuncturedFamily

/-!
# The normalized smooth atlas on the actual punctured complete one-gon family

The constructed etale cover of the punctured complete base maps to the
original normalized slice. On every affine test, its normalized cubic is
the actual pullback of the original complete boundary family, retaining
the complete coefficient map and the original infinity marking.
-/

@[expose] public noncomputable section
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
namespace FLT.Mazur.OneGonSmoothing
open UniversalWeierstrass WeierstrassIntegralChart
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
variable (R : Type) [CommRing R] (h₂ : IsUnit (2 : R))

/-- The actual auxiliary etale cover of the punctured complete boundary base. -/
abbrev puncturedAtlas := smoothAuxiliaryCover (puncturedParameter R)
  (puncturedTwo_isUnit R h₂) (puncturedParameter_isUnit R) (puncturedFactor_isUnit R)

/-- The actual source scheme of the punctured auxiliary cover. -/
abbrev puncturedAtlasScheme := smoothAuxiliaryOverlap (puncturedParameter R)
  (puncturedTwo_isUnit R h₂) (puncturedParameter_isUnit R) (puncturedFactor_isUnit R)

/-- The original projection of the punctured auxiliary cover. -/
abbrev puncturedAtlasProjection := smoothAuxiliaryProjection (puncturedParameter R)
  (puncturedTwo_isUnit R h₂) (puncturedParameter_isUnit R) (puncturedFactor_isUnit R)

/-- The actual retained level-four point of the punctured boundary cover. -/
abbrev puncturedAtlasPoint := smoothAuxiliaryPoint (puncturedParameter R)
  (puncturedTwo_isUnit R h₂) (puncturedParameter_isUnit R) (puncturedFactor_isUnit R)

/-- The entire etale cover maps to the original normalized smooth slice. -/
def puncturedAtlasNormalized : puncturedAtlasScheme R h₂ ⟶ normalizedSlice :=
  smoothNormalizedOverlap (puncturedParameter R) (puncturedTwo_isUnit R h₂)
    (puncturedParameter_isUnit R) (puncturedFactor_isUnit R)

variable {S : Type} [CommRing S] (j : Spec (.of S) ⟶ puncturedAtlasScheme R h₂)

/-- The original complete coefficient map on an actual affine atlas test. -/
def puncturedAtlasCoefficient : PowerSeries R →+* S :=
  (smoothOverlapCoefficient (puncturedParameter R) (puncturedTwo_isUnit R h₂)
    (puncturedParameter_isUnit R) (puncturedFactor_isUnit R) j).comp
      (algebraMap (PowerSeries R) (PuncturedRing R))

/-- The complete coefficient map retains the actual map to the complete base. -/
theorem puncturedAtlasCoefficient_spec :
    Spec.map (CommRingCat.ofHom (puncturedAtlasCoefficient R h₂ j)) =
      (j ≫ puncturedAtlasProjection R h₂) ≫ puncturedBaseInclusion R := by
  rw [puncturedAtlasCoefficient, ← smoothOverlapCoefficient_spec]
  exact Spec.map_comp _ _

/-- The normalized atlas morphism restricts to the original affine normalization. -/
theorem puncturedAtlasNormalized_affine :
    j ≫ puncturedAtlasNormalized R h₂ =
      auxiliaryFamilyNormalizedSlicePoint (j ≫ puncturedAtlasPoint R h₂) :=
  smoothNormalizedOverlap_affine _ _ _ _ _

/-- The normalized cubic on an atlas test is the original complete-family pullback. -/
def puncturedAtlasFamilyIso :
    integralCurve (auxiliaryPullbackEquation (auxiliaryPointSections
      (auxiliaryFamilyNormalizedPoint (j ≫ puncturedAtlasPoint R h₂)))) ≅
        pullback (family (PowerSeries.X : PowerSeries R)).hom
          (Spec.map (CommRingCat.ofHom (puncturedAtlasCoefficient R h₂ j))) :=
  let _ := (puncturedAtlasCoefficient R h₂ j).toAlgebra
  smoothOverlapFamilyIso (puncturedParameter R) (puncturedTwo_isUnit R h₂)
    (puncturedParameter_isUnit R) (puncturedFactor_isUnit R) j ≪≫
      coefficientPullbackIso (R := PowerSeries R) (S := S) PowerSeries.X

/-- The normalized comparison retains the actual map to the complete base. -/
@[reassoc] theorem puncturedAtlasFamilyIso_snd :
    (puncturedAtlasFamilyIso R h₂ j).hom ≫ pullback.snd _ _ =
      integralCurveStructure (auxiliaryPullbackEquation (auxiliaryPointSections
        (auxiliaryFamilyNormalizedPoint (j ≫ puncturedAtlasPoint R h₂)))) := by
  let _ := (puncturedAtlasCoefficient R h₂ j).toAlgebra
  let e := smoothOverlapFamilyIso (puncturedParameter R) (puncturedTwo_isUnit R h₂)
    (puncturedParameter_isUnit R) (puncturedFactor_isUnit R) j
  exact (Category.assoc _ _ _).trans
    ((congrArg (fun g => e.hom ≫ g)
      (coefficientPullbackIso_snd (R := PowerSeries R) (S := S) PowerSeries.X)).trans
        (smoothNormalizedIso_base _ _ _ _ _ _))

/-- The infinity section remains the original marked section of the complete family. -/
@[reassoc] theorem puncturedAtlasFamilyIso_zero_fst :
    integralCurveZero (auxiliaryPullbackEquation (auxiliaryPointSections
      (auxiliaryFamilyNormalizedPoint (j ≫ puncturedAtlasPoint R h₂)))) ≫
        (puncturedAtlasFamilyIso R h₂ j).hom ≫ pullback.fst _ _ =
          Spec.map (CommRingCat.ofHom (puncturedAtlasCoefficient R h₂ j)) ≫
            marking (PowerSeries.X : PowerSeries R) := by
  let _ := (puncturedAtlasCoefficient R h₂ j).toAlgebra
  let e := smoothOverlapFamilyIso (puncturedParameter R) (puncturedTwo_isUnit R h₂)
    (puncturedParameter_isUnit R) (puncturedFactor_isUnit R) j
  have hz := smoothOverlapFamilyIso_zero (puncturedParameter R) (puncturedTwo_isUnit R h₂)
    (puncturedParameter_isUnit R) (puncturedFactor_isUnit R) j
  have hc := coefficientPullbackIso_fst (R := PowerSeries R) (S := S) PowerSeries.X
  change _ ≫ (e.hom ≫ _) ≫ _ = _
  rw [Category.assoc]
  let z := integralCurveZero (auxiliaryPullbackEquation (auxiliaryPointSections
    (auxiliaryFamilyNormalizedPoint (j ≫ puncturedAtlasPoint R h₂))))
  exact (congrArg (fun g => z ≫ e.hom ≫ g) hc).trans
    ((Category.assoc _ _ _).symm.trans
      ((congrArg (fun g =>
        g ≫ coefficientMorphism (R := PowerSeries R) (S := S) PowerSeries.X) hz).trans
        (marking_coefficientMorphism (R := PowerSeries R) (S := S) PowerSeries.X)))

end FLT.Mazur.OneGonSmoothing
