/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.BaseAdicReesSpectrumTripleSheafNormalization

/-!
# The full triple-overlap coefficient cocycle

The global pair comparisons compose after transport to common coordinate
sheaves on the entire scheme-theoretic triple overlap.
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
attribute [local irreducible] spectrumOverlapChart spectrumSpaceMap
attribute [local irreducible] spectrumSheaf spectrumAffineOverlap
attribute [local irreducible] spectrumOverlapSheafIso spectrumTripleOverlapChart
attribute [local irreducible] spectrumTripleFirstSheafMap spectrumTripleLastSheafMap
attribute [local irreducible] spectrumTripleOuterSheafMap

/-- The normalized full-overlap coefficient isomorphisms satisfy the global cocycle. -/
theorem spectrumTripleSheafMap_cocycle (U V T : X.affineOpens) :
    spectrumTripleFirstSheafMap f J M U V T ≫
        spectrumTripleLastSheafMap f J M U V T =
      spectrumTripleOuterSheafMap f J M U V T := by
  apply spectrumTripleOverlap_hom_ext f J U V T
  intro W i j k
  apply (cancel_mono ((comparison (spectrumTripleOverlapChart f J i j k)
    (spectrumTripleThirdProjection f J U V T) (spectrumMap f J k)
    (spectrumTripleOverlapChart_third f J i j k)).hom.app
      (spectrumSheaf f J M T))).mp
  rw [Functor.map_comp, Category.assoc, spectrumTripleLastSheafMap_chart,
    ← Category.assoc, spectrumTripleFirstSheafMap_chart, Category.assoc,
    spectrumOverlapAffineMap_cocycle, spectrumTripleOuterSheafMap_chart]

end FLT.Mazur.BaseAdicRees
