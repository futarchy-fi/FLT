/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.OneGonSmoothingOverlapGroup
public import FLT.Mazur.OneGonSmoothingNormalizedOverlap
public import FLT.Mazur.UniversalWeierstrassAuxiliarySchemeGroupComparison

/-!
# Normalized one-gon comparison on arbitrary source schemes

The normalized universal family and the original boundary pullback are
isomorphic as group schemes on every source of the actual auxiliary overlap.
The comparison uses the existing coefficient and proper normalization maps.
-/

@[expose] public noncomputable section
open CategoryTheory AlgebraicGeometry
namespace FLT.Mazur.OneGonSmoothing
open UniversalWeierstrass WeierstrassIntegralChart
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
variable {R : Type} [CommRing R]
  (t : R) (h₂ : IsUnit (2 : R)) (ht : IsUnit t) (hf : IsUnit (1 + 432 * t))
  {T : Scheme} (j : T ⟶ smoothAuxiliaryOverlap t h₂ ht hf)

/-- The original full auxiliary family is the actual boundary group over any overlap test. -/
irreducible_def smoothSchemeAuxiliaryGroupIso :
    auxiliarySchemeGroup (j ≫ smoothAuxiliaryPoint t h₂ ht hf) ≅
      smoothOverlapGroup t h₂ ht hf j :=
  GroupSchemeBaseChange.congrIso
      ((Category.assoc _ _ _).trans
        ((congrArg (fun k => j ≫ k) (smoothAuxiliaryPoint_base t h₂ ht hf)).trans
          (Category.assoc _ _ _).symm)) _ ≪≫
    GroupSchemeBaseChange.compIso (j ≫ smoothAuxiliaryProjection t h₂ ht hf)
      (Spec.map (CommRingCat.ofHom (smoothParameter t h₂ ht hf)))
      (integralCurveGroup smoothEquation smoothEquation_discriminant) ≪≫
    (Over.pullback (j ≫ smoothAuxiliaryProjection t h₂ ht hf)).mapCommGrp.mapIso
      (smoothUniversalGroupIso t h₂ ht hf).symm

/-- Actual normalization compares with the original boundary group on arbitrary schemes. -/
irreducible_def smoothSchemeNormalizedGroupIso :
    auxiliarySchemeGroup
      (auxiliarySchemeNormalizedPoint (j ≫ smoothAuxiliaryPoint t h₂ ht hf)) ≅
        smoothOverlapGroup t h₂ ht hf j :=
  auxiliarySchemeNormalizationGroupIso (j ≫ smoothAuxiliaryPoint t h₂ ht hf) ≪≫
    smoothSchemeAuxiliaryGroupIso t h₂ ht hf j

/-- The arbitrary-source normalization retains its actual map into the original slice. -/
theorem smoothNormalizedOverlap_scheme :
    j ≫ smoothNormalizedOverlap t h₂ ht hf =
      auxiliarySchemeNormalizedSlicePoint (j ≫ smoothAuxiliaryPoint t h₂ ht hf) :=
  (auxiliarySchemeNormalizedSlicePoint_natural
    (smoothAuxiliaryPoint t h₂ ht hf) j).symm

/-- The compared normalized point is the original normalized-slice morphism on the test. -/
theorem smoothNormalizedOverlap_scheme_point :
    (j ≫ smoothNormalizedOverlap t h₂ ht hf) ≫ normalizedSliceInclusion =
      auxiliarySchemeNormalizedPoint (j ≫ smoothAuxiliaryPoint t h₂ ht hf) := by
  rw [smoothNormalizedOverlap_scheme, auxiliarySchemeNormalizedSlicePoint_inclusion]

/-- Forgetting groups gives a comparison of the actual original proper families over the test. -/
def smoothSchemeNormalizedOverIso :
    (auxiliarySchemeGroup
      (auxiliarySchemeNormalizedPoint (j ≫ smoothAuxiliaryPoint t h₂ ht hf))).X ≅
        (smoothOverlapGroup t h₂ ht hf j).X :=
  (CommGrp.forget (Over T)).mapIso (smoothSchemeNormalizedGroupIso t h₂ ht hf j)

/-- The comparison retains the complete original source base. -/
@[reassoc] theorem smoothSchemeNormalizedOverIso_base :
    (smoothSchemeNormalizedOverIso t h₂ ht hf j).hom.left ≫
      (smoothOverlapGroup t h₂ ht hf j).X.hom =
        (auxiliarySchemeGroup
          (auxiliarySchemeNormalizedPoint (j ≫ smoothAuxiliaryPoint t h₂ ht hf))).X.hom :=
  (smoothSchemeNormalizedOverIso t h₂ ht hf j).hom.w

end FLT.Mazur.OneGonSmoothing
