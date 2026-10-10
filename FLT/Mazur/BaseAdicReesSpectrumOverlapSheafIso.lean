/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.BaseAdicReesSpectrumOverlapCompatibility
public import FLT.Mazur.BaseAdicReesSpectrumOverlapSheafMap

/-!
# Isomorphisms on full relative Rees chart overlaps

The compatible original coefficient comparisons glue on the entire
scheme-theoretic overlap. Their pullbacks recover the supplied affine maps.
-/

@[expose] public noncomputable section

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option backward.defeqAttrib.useBackward true

open CategoryTheory AlgebraicGeometry
open Scheme.Modules

universe u

namespace FLT.Mazur.BaseAdicRees

open ModuleSheafOpenImmersionGluing

variable {R : CommRingCat.{u}} {X : Scheme.{u}} (f : X ⟶ Spec R)
  (J : Ideal R) [IsLocallyNoetherian X] (M : X.Modules) [M.IsFinitePresentation]
  (U V : X.affineOpens)

attribute [local irreducible] Scheme.Modules.pullback spectrumOverlapSheafMap
attribute [local irreducible] AffineIteratedPullbackSections.compositeIso

/-- The actual affine overlap maps satisfy the full gluing compatibility condition. -/
lemma spectrumOverlapSheafMaps_compatible :
    Compatible (fun W : {W : X.affineOpens // W.1 ≤ U.1 ∧ W.1 ≤ V.1} ↦
        modelSpectrum f J W.val)
      (fun W ↦ spectrumOverlapChart f J W.property.1 W.property.2)
      (fun W ↦ spectrumOverlapSheafMap f J M W.property.1 W.property.2) := by
  exact spectrumOverlapMaps_compatible f J U V _ _
    (fun _ h k ↦ spectrumOverlapSheafMap f J M h k)
    (fun _ _ h k l ↦ spectrumOverlapSheafMap_refine f J M h k l)

/-- The global comparison of the two model sheaves on their full relative overlap. -/
def spectrumOverlapSheafIso :
    (pullback (spectrumOverlapFirst f J U V)).obj
        (spectrumSheaf f J M U) ≅
      (pullback (spectrumOverlapSecond f J U V)).obj
        (spectrumSheaf f J M V) :=
  glueIso (fun W : {W : X.affineOpens // W.1 ≤ U.1 ∧ W.1 ≤ V.1} ↦
      modelSpectrum f J W.val)
    (fun W ↦ spectrumOverlapChart f J W.property.1 W.property.2)
    (fun x ↦ by
      obtain ⟨W, h, k, hx⟩ := spectrumOverlapChart_jointly_surjective f J U V x
      exact ⟨⟨W, h, k⟩, hx⟩)
    (fun W ↦ spectrumOverlapSheafMap f J M W.property.1 W.property.2)
    (spectrumOverlapSheafMaps_compatible f J M U V) (fun _ ↦ inferInstance)

/-- Restricting the full-overlap comparison recovers each original affine comparison. -/
lemma spectrumOverlapSheafIso_pullback {W : X.affineOpens} (h : W.1 ≤ U.1) (k : W.1 ≤ V.1) :
    (pullback (spectrumOverlapChart f J h k)).map (spectrumOverlapSheafIso f J M U V).hom =
      spectrumOverlapSheafMap f J M h k := by
  unfold spectrumOverlapSheafIso glueIso
  exact pullback_glue
    (fun T : {T : X.affineOpens // T.1 ≤ U.1 ∧ T.1 ≤ V.1} ↦ modelSpectrum f J T.val)
    (fun T ↦ spectrumOverlapChart f J T.property.1 T.property.2)
    (fun x ↦ by
      obtain ⟨Z, i, j, hx⟩ := spectrumOverlapChart_jointly_surjective f J U V x
      exact ⟨⟨Z, i, j⟩, hx⟩)
    (fun T ↦ spectrumOverlapSheafMap f J M T.property.1 T.property.2)
    (spectrumOverlapSheafMaps_compatible f J M U V)
    (⟨W, h, k⟩ : {W : X.affineOpens // W.1 ≤ U.1 ∧ W.1 ≤ V.1})

end FLT.Mazur.BaseAdicRees
