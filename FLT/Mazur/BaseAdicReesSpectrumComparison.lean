/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.BaseAdicReesSpectrum

/-!
# Geometric composition on fixed Rees spectra

The original composition comparison agrees with geometric pullback composition.
This equality keeps tensor definitions out of subsequent refinement proofs.
-/

@[expose] public noncomputable section

set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency.types false

open CategoryTheory AlgebraicGeometry
open Scheme.Modules
open scoped TensorProduct

universe u

namespace FLT.Mazur.BaseAdicRees

variable {R : CommRingCat.{u}} {X : Scheme.{u}} (f : X ⟶ Spec R)
  (J : Ideal R) [IsLocallyNoetherian X] (M : X.Modules) [M.IsFinitePresentation]

attribute [local irreducible] Scheme.Modules.pullback
attribute [local irreducible] modelMap
attribute [local irreducible] chartSpaceMap modelSheaf
attribute [local irreducible] modelAffineOverlap spectrumAffineOverlap
attribute [local semireducible] modelSpectrum spectrumAffineOverlap
attribute [local irreducible] modelCompositeIso
attribute [local irreducible] AffineIteratedPullbackSections.compositeIso

/-- Iterated original restrictions on the fixed spectrum presentation. -/
def spectrumCompositeIso {U V W : X.affineOpens} (i : U.1 ≤ V.1) (j : V.1 ≤ W.1) :
    (pullback (spectrumMap f J i)).obj
        ((pullback (spectrumMap f J j)).obj (spectrumSheaf f J M W)) ≅
      (pullback (spectrumMap f J (i.trans j))).obj (spectrumSheaf f J M W) :=
  modelCompositeIso f J M i j

/-- The fixed presentation uses the actual geometric pullback comparison. -/
lemma spectrumCompositeIso_eq {U V W : X.affineOpens} (i : U.1 ≤ V.1) (j : V.1 ≤ W.1) :
    spectrumCompositeIso f J M i j =
      AffineIteratedPullbackSections.compositeIso
        (spectrumMap f J i) (spectrumMap f J j) (spectrumMap f J (i.trans j))
        (spectrumMap_comp f J i j) (spectrumSheaf f J M W) :=
  modelCompositeIso_eq_chart f J M i j

/-- Original comparisons refine in the fixed spectrum presentation. -/
lemma spectrumAffineOverlap_refine {U V W Z : X.affineOpens}
    (i : W.1 ≤ U.1) (j : W.1 ≤ V.1) (k : Z.1 ≤ W.1) :
    (pullback (spectrumMap f J k)).map (spectrumAffineOverlap f J M i j).hom ≫
        (spectrumCompositeIso f J M k j).hom =
      (spectrumCompositeIso f J M k i).hom ≫
        (spectrumAffineOverlap f J M (k.trans i) (k.trans j)).hom :=
  modelAffineOverlap_refine f J M i j k

end FLT.Mazur.BaseAdicRees
