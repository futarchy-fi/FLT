/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.BaseAdicReesGeometricRefinement

/-!
# Fixed spectrum presentations of the Rees models

Naming the spectrum fixes all scalar instances before specializing geometric
pullback identities. The sheaves and comparisons retain their original definitions.
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
attribute [local irreducible] modelAffineOverlap
attribute [local irreducible] AffineIteratedPullbackSections.compositeIso

/-- The tensor spectrum of an original affine chart, with its scalar structure fixed. -/
@[irreducible]
def modelSpectrum (V : X.affineOpens) : Scheme.{u} :=
  let _ := chartAlgebra f V
  Spec (.of (Γ(X, V.1) ⊗[R] reesAlgebra J))

/-- The original chart inclusion in the fixed spectrum presentation. -/
def spectrumMap {U V : X.affineOpens} (i : U.1 ≤ V.1) :
    modelSpectrum f J U ⟶ modelSpectrum f J V := by
  unfold modelSpectrum
  exact modelMap f J i

/-- The original finite model sheaf on its fixed spectrum presentation. -/
def spectrumSheaf (V : X.affineOpens) : (modelSpectrum f J V).Modules := by
  unfold modelSpectrum
  exact modelSheaf f J V M

omit [IsLocallyNoetherian X] in
/-- Original inclusions compose in the fixed spectrum presentation. -/
lemma spectrumMap_comp {U V W : X.affineOpens} (i : U.1 ≤ V.1) (j : V.1 ≤ W.1) :
    spectrumMap f J i ≫ spectrumMap f J j = spectrumMap f J (i.trans j) := by
  unfold spectrumMap modelSpectrum
  exact modelMap_comp f J i j

/-- The normalized original affine comparison in the fixed spectrum presentation. -/
def spectrumAffineOverlap {U V W : X.affineOpens} (i : W.1 ≤ U.1) (j : W.1 ≤ V.1) :
    (pullback (spectrumMap f J i)).obj (spectrumSheaf f J M U) ≅
      (pullback (spectrumMap f J j)).obj (spectrumSheaf f J M V) := by
  unfold spectrumMap spectrumSheaf modelSpectrum
  exact modelAffineOverlap f J M i j

end FLT.Mazur.BaseAdicRees
