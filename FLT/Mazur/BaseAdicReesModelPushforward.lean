/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.BaseAdicReesModelDescent
public import FLT.Mazur.AffinePushforwardQuasicoherent
public import FLT.Mazur.ModuleSheafTensorRestrict

/-!
# Affine direct image of the original global Rees model

The source projection is affine. Its actual pushforward recovers the
original finite Rees sheaf on each original tensor chart, through the
chart identification already proved for the descended global model.
-/

@[expose] public noncomputable section

set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency.types false

open CategoryTheory Limits AlgebraicGeometry
open Scheme.Modules

universe u

namespace FLT.Mazur.BaseAdicRees

variable {R : CommRingCat.{u}} {X : Scheme.{u}} (f : X ⟶ Spec R) (J : Ideal R)

/-- The actual projection of the relative Rees space to the original scheme. -/
def modelSourceProjection : relativeSpace f J ⟶ X := pullback.fst f (baseMap J)

/-- The relative Rees space is affine over the original scheme. -/
instance modelSourceProjection_isAffineHom : IsAffineHom (modelSourceProjection f J) := by
  unfold modelSourceProjection
  exact MorphismProperty.pullback_fst f (baseMap J)
    (inferInstanceAs (IsAffineHom (baseMap J)))

variable [IsLocallyNoetherian X] (M : X.Modules) [M.IsFinitePresentation]

attribute [local irreducible] globalModelSheaf modelSheaf chartSpaceMap

/-- The original descended model, pushed forward along the actual affine projection. -/
def modelPushforward : X.Modules :=
  (pushforward (modelSourceProjection f J)).obj (globalModelSheaf f J M)

/-- Affine direct image retains quasi-coherence of the original model. -/
instance modelPushforward_isQuasicoherent [IsNoetherianRing R] :
    (modelPushforward f J M).IsQuasicoherent :=
  FCurve.affinePushforward_isQuasicoherent (modelSourceProjection f J) (globalModelSheaf f J M)

/-- Actual direct-image sections on a source chart are sections of the original model chart. -/
def modelPushforwardChartSectionsIso (V : X.affineOpens) :
    Γ(modelPushforward f J M, V.1) ≅ Γ(modelSheaf f J V M, ⊤) := by
  let i := chartSpaceMap f J V
  have hi : i ''ᵁ ⊤ = modelSourceProjection f J ⁻¹ᵁ V.1 :=
    i.image_top_eq_opensRange.trans (chartSpaceMap_opensRange f J V)
  exact (globalModelSheaf f J M).presheaf.mapIso (eqToIso hi).op ≪≫
    ((globalModelSheaf f J M).restrictAppIso i ⊤).symm ≪≫
    (FCurve.ModuleSheafTensor.sectionsCongr
      (globalModelSheafChartIso f J M V) ⊤).toAddEquiv.toAddCommGrpIso

end FLT.Mazur.BaseAdicRees
