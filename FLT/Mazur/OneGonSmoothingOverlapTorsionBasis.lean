/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.OneGonSmoothingSchemeNormalizedGroup
public import FLT.Mazur.UniversalWeierstrassAuxiliaryNormalizedTorsionBasis

/-!
# The full torsion basis on the original one-gon overlap group

The original auxiliary sixteen-section scheme is pulled back along the actual
retained auxiliary point. It identifies the entire four-torsion equalizer of
the boundary group, including on nonaffine or nonreduced source schemes.
-/

@[expose] public noncomputable section
open CategoryTheory AlgebraicGeometry
namespace FLT.Mazur.OneGonSmoothing
open UniversalWeierstrass
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
variable {R : Type} [CommRing R]
  (t : R) (h₂ : IsUnit (2 : R)) (ht : IsUnit t) (hf : IsUnit (1 + 432 * t))
  {T : Scheme} (j : T ⟶ smoothAuxiliaryOverlap t h₂ ht hf)

/-- The original constant-label scheme identifies the full torsion of the auxiliary test group. -/
def smoothSchemeAuxiliaryTorsionBasis :
    (Over.pullback (j ≫ smoothAuxiliaryPoint t h₂ ht hf)).obj
      (Over.mk auxiliaryConstantLabelsMap) ≅
        GroupTorsionScheme.scheme
          (auxiliarySchemeGroup (j ≫ smoothAuxiliaryPoint t h₂ ht hf)).X 4 :=
  auxiliaryBaseChangedFullBasis (j ≫ smoothAuxiliaryPoint t h₂ ht hf) ≪≫
    (Over.pullbackComp (j ≫ smoothAuxiliaryPoint t h₂ ht hf) levelFour.hom).symm.app
      fourTorsion ≪≫
    GroupTorsionScheme.baseChangeIso
      ((j ≫ smoothAuxiliaryPoint t h₂ ht hf) ≫ levelFour.hom) universalGroup 4

attribute [local irreducible] smoothOverlapGroup auxiliarySchemeGroup

/-- The entire original auxiliary basis is retained on the actual boundary group. -/
def smoothOverlapTorsionBasis :
    (Over.pullback (j ≫ smoothAuxiliaryPoint t h₂ ht hf)).obj
      (Over.mk auxiliaryConstantLabelsMap) ≅
        GroupTorsionScheme.scheme (smoothOverlapGroup t h₂ ht hf j).X 4 :=
  smoothSchemeAuxiliaryTorsionBasis t h₂ ht hf j ≪≫
    GroupTorsionScheme.transportIso
      (auxiliarySchemeGroup (j ≫ smoothAuxiliaryPoint t h₂ ht hf))
      (smoothOverlapGroup t h₂ ht hf j) (smoothSchemeAuxiliaryGroupIso t h₂ ht hf j) 4

/-- The same original full basis is retained by the normalized actual group family. -/
def smoothSchemeNormalizedTorsionBasis :
    (Over.pullback (j ≫ smoothAuxiliaryPoint t h₂ ht hf)).obj
      (Over.mk auxiliaryConstantLabelsMap) ≅
        GroupTorsionScheme.scheme (auxiliarySchemeGroup
          (auxiliarySchemeNormalizedPoint (j ≫ smoothAuxiliaryPoint t h₂ ht hf))).X 4 :=
  smoothOverlapTorsionBasis t h₂ ht hf j ≪≫
    GroupTorsionScheme.transportIso (smoothOverlapGroup t h₂ ht hf j)
      (auxiliarySchemeGroup
        (auxiliarySchemeNormalizedPoint (j ≫ smoothAuxiliaryPoint t h₂ ht hf)))
      (smoothSchemeNormalizedGroupIso t h₂ ht hf j).symm 4

end FLT.Mazur.OneGonSmoothing
