/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.DivisorLinePullbackTransport
public import FLT.Mazur.PolygonInfinitesimalStageAmple

/-!
# Coherence of the actual ample boundary-line system

The canonical line comparisons on all infinitesimal polygon transitions
satisfy identity and composition, with the specified scheme pullback unitors,
compositors and equality transports. These are laws for the previously
constructed comparisons, not replacement choices of line isomorphisms.
-/

@[expose] public noncomputable section

open CategoryTheory AlgebraicGeometry
open AlgebraicGeometry.Scheme.Modules

set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true

namespace FLT.Mazur.PolygonInfinitesimalStages

open FCurve

variable (R : Type*) [CommRing R] (n : ℕ) (h : 2 ≤ n)

/-- The actual boundary-line comparison at an identity is the pullback identity comparison. -/
theorem boundaryLineSystemIso_id (a : ℕ) :
    boundaryLineSystemIso R n h (𝟙 a) =
      (pullbackCongr ((stageSystem R n h).map_id a)).app (boundaryLine R a n h) ≪≫
        (pullbackId ((family R a n h).left)).app (boundaryLine R a n h) :=
  divisorLinePullbackIsoOfEq_id_eq _ ((stageSystem R n h).map_id a)
    (boundaryIdeal R a n h) (boundaryIdeal_cartier R a n h).1
    (boundaryIdeal_systemMap R n h (𝟙 a))

/-- The actual ample-line comparisons obey the pullback composition law on every transition. -/
theorem boundaryLineSystemIso_comp {a b c : ℕ} (f : a ⟶ b) (g : b ⟶ c) :
    (pullback ((stageSystem R n h).map f)).mapIso (boundaryLineSystemIso R n h g) ≪≫
        boundaryLineSystemIso R n h f =
      (pullbackComp ((stageSystem R n h).map f) ((stageSystem R n h).map g)).app
          (boundaryLine R c n h) ≪≫
        (pullbackCongr ((stageSystem R n h).map_comp f g).symm).app
          (boundaryLine R c n h) ≪≫ boundaryLineSystemIso R n h (f ≫ g) :=
  divisorLinePullbackIsoOfEq_comp_eq _ _ _ ((stageSystem R n h).map_comp f g)
    (boundaryIdeal_cartier R c n h).1 (boundaryIdeal_cartier R b n h).1
    (boundaryIdeal_cartier R a n h).1 (boundaryIdeal_systemMap R n h g)
    (boundaryIdeal_systemMap R n h f) (boundaryIdeal_systemMap R n h (f ≫ g))

end FLT.Mazur.PolygonInfinitesimalStages
