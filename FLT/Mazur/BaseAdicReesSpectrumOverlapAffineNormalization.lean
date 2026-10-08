/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.BaseAdicReesSpectrumOverlapSheafIso

/-!
# Affine normalization of the glued coefficient comparisons

The full-overlap isomorphisms recover the original normalized affine maps.
Consequently their normalized restrictions satisfy the affine cocycle.
-/

@[expose] public noncomputable section

set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency.types false

open CategoryTheory AlgebraicGeometry
open Scheme.Modules

universe u

namespace FLT.Mazur.BaseAdicRees

open SheafPullbackPathComparison

variable {R : CommRingCat.{u}} {X : Scheme.{u}} (f : X ⟶ Spec R)
  (J : Ideal R) [IsLocallyNoetherian X] (M : X.Modules) [M.IsFinitePresentation]

attribute [local irreducible] Scheme.Modules.pullback spectrumMap
attribute [local irreducible] spectrumOverlapChart
attribute [local irreducible] spectrumSheaf spectrumAffineOverlap
attribute [local irreducible] AffineIteratedPullbackSections.compositeIso

/-- Normalize the restriction of the full-overlap comparison to an affine chart. -/
def spectrumOverlapAffineMap {U V W : X.affineOpens}
    (i : W.1 ≤ U.1) (j : W.1 ≤ V.1) :
    (pullback (spectrumMap f J i)).obj (spectrumSheaf f J M U) ⟶
      (pullback (spectrumMap f J j)).obj (spectrumSheaf f J M V) :=
  (comparison (X := modelSpectrum f J W)
      (spectrumOverlapChart f J i j) (spectrumOverlapFirst f J U V)
      (spectrumMap f J i) (spectrumOverlapChart_first f J i j)).inv.app
        (spectrumSheaf f J M U) ≫
    (pullback (X := modelSpectrum f J W)
      (spectrumOverlapChart f J i j)).map (spectrumOverlapSheafIso f J M U V).hom ≫
    (comparison (X := modelSpectrum f J W)
      (spectrumOverlapChart f J i j) (spectrumOverlapSecond f J U V)
      (spectrumMap f J j) (spectrumOverlapChart_second f J i j)).hom.app
        (spectrumSheaf f J M V)

/-- The normalized global comparison is the original affine coefficient comparison. -/
lemma spectrumOverlapAffineMap_eq {U V W : X.affineOpens}
    (i : W.1 ≤ U.1) (j : W.1 ≤ V.1) :
    spectrumOverlapAffineMap f J M i j =
      (spectrumAffineOverlap f J M i j).hom := by
  unfold spectrumOverlapAffineMap
  rw [spectrumOverlapSheafIso_pullback]
  unfold spectrumOverlapSheafMap SheafPullbackLocalComparison.transport
  simp only [Category.assoc, Iso.inv_hom_id_app_assoc, Iso.inv_hom_id_app, Category.comp_id]

/-- The normalized full-overlap comparisons compose on every common affine chart. -/
lemma spectrumOverlapAffineMap_cocycle {U V T W : X.affineOpens}
    (i : W.1 ≤ U.1) (j : W.1 ≤ V.1) (k : W.1 ≤ T.1) :
    spectrumOverlapAffineMap f J M i j ≫
        spectrumOverlapAffineMap f J M j k =
      spectrumOverlapAffineMap f J M i k := by
  rw [spectrumOverlapAffineMap_eq, spectrumOverlapAffineMap_eq,
    spectrumOverlapAffineMap_eq]
  unfold spectrumAffineOverlap spectrumSheaf spectrumMap modelSpectrum
  exact modelAffineOverlap_cocycle f J M i j k

end FLT.Mazur.BaseAdicRees
