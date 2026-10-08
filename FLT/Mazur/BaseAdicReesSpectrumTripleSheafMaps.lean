/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.BaseAdicReesSpectrumOverlapAffineNormalization
public import FLT.Mazur.BaseAdicReesSpectrumTripleProjections
public import FLT.Mazur.SheafPullbackMapNormalization

/-!
# Coefficient maps on the relative triple overlap

Normalize each pair comparison to the same three coordinate pullbacks.
This makes their composition an equality of actual module-sheaf morphisms.
-/

@[expose] public noncomputable section

set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency.types false

open CategoryTheory AlgebraicGeometry
open Scheme.Modules

universe u

namespace FLT.Mazur.BaseAdicRees

open SheafPullbackMapNormalization

variable {R : CommRingCat.{u}} {X : Scheme.{u}} (f : X ⟶ Spec R)
  (J : Ideal R) [IsLocallyNoetherian X] (M : X.Modules) [M.IsFinitePresentation]
  (U V T : X.affineOpens)

attribute [local irreducible] Scheme.Modules.pullback spectrumMap
attribute [local irreducible] spectrumOverlapChart spectrumSpaceMap
attribute [local irreducible] spectrumSheaf spectrumAffineOverlap
attribute [local irreducible] AffineIteratedPullbackSections.compositeIso
attribute [local irreducible] spectrumOverlapSheafIso

/-- The first pair comparison on common triple-coordinate sheaves. -/
def spectrumTripleFirstSheafMap :
    (pullback (spectrumTripleFirstProjection f J U V T)).obj
        (spectrumSheaf f J M U) ⟶
      (pullback (spectrumTripleSecondProjection f J U V T)).obj
        (spectrumSheaf f J M V) :=
  normalize (spectrumTripleFirstPairProjection f J U V T)
    (spectrumOverlapFirst f J U V) (spectrumOverlapSecond f J U V)
    (spectrumTripleFirstProjection f J U V T) (spectrumTripleSecondProjection f J U V T)
    rfl rfl (spectrumOverlapSheafIso f J M U V).hom

/-- The last pair comparison on common triple-coordinate sheaves. -/
def spectrumTripleLastSheafMap :
    (pullback (spectrumTripleSecondProjection f J U V T)).obj
        (spectrumSheaf f J M V) ⟶
      (pullback (spectrumTripleThirdProjection f J U V T)).obj
        (spectrumSheaf f J M T) :=
  normalize (spectrumTripleLastPairProjection f J U V T)
    (spectrumOverlapFirst f J V T) (spectrumOverlapSecond f J V T)
    (spectrumTripleSecondProjection f J U V T) (spectrumTripleThirdProjection f J U V T)
    (spectrumTripleLastPairProjection_second f J U V T)
    (spectrumTripleLastPairProjection_third f J U V T) (spectrumOverlapSheafIso f J M V T).hom

/-- The outer pair comparison on common triple-coordinate sheaves. -/
def spectrumTripleOuterSheafMap :
    (pullback (spectrumTripleFirstProjection f J U V T)).obj
        (spectrumSheaf f J M U) ⟶
      (pullback (spectrumTripleThirdProjection f J U V T)).obj
        (spectrumSheaf f J M T) :=
  normalize (spectrumTripleOuterPairProjection f J U V T)
    (spectrumOverlapFirst f J U T) (spectrumOverlapSecond f J U T)
    (spectrumTripleFirstProjection f J U V T) (spectrumTripleThirdProjection f J U V T)
    (spectrumTripleOuterPairProjection_first f J U V T)
    (spectrumTripleOuterPairProjection_third f J U V T) (spectrumOverlapSheafIso f J M U T).hom

/-- The first pair comparison remains invertible on the triple overlap. -/
instance spectrumTripleFirstSheafMap_isIso :
    IsIso (spectrumTripleFirstSheafMap f J M U V T) := by
  unfold spectrumTripleFirstSheafMap
  infer_instance

/-- The last pair comparison remains invertible on the triple overlap. -/
instance spectrumTripleLastSheafMap_isIso :
    IsIso (spectrumTripleLastSheafMap f J M U V T) := by
  unfold spectrumTripleLastSheafMap
  infer_instance

/-- The outer pair comparison remains invertible on the triple overlap. -/
instance spectrumTripleOuterSheafMap_isIso :
    IsIso (spectrumTripleOuterSheafMap f J M U V T) := by
  unfold spectrumTripleOuterSheafMap
  infer_instance

end FLT.Mazur.BaseAdicRees
