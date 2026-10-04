/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.ProjectiveTwistingSheafTensor
public import FLT.Mazur.AmpleAffinePullback

/-!
# Global-section coordinates in a cocycle trivialization

The chart trivialization and the ambient coefficient evaluation agree through
the canonical global-section isomorphism of the open subscheme.
-/

@[expose] public noncomputable section
open CategoryTheory AlgebraicGeometry TopologicalSpace
universe u
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
namespace FLT.Mazur.FCurve.ModuleSheafUnitCocycle.Cocycle
variable {X : Scheme.{u}} {ι : Type u} {U : ι → X.Opens} (g : Cocycle U)

/-- Successive restrictions of cocycle sections compose. -/
lemma restrict_restrict {V W Z : X.Opens} (h : W ≤ V) (h' : Z ≤ W) (s : g.sections V) :
    g.restrict h' (g.restrict h s) = g.restrict (h'.trans h) s := by
  ext i
  exact res_res _ _ _

/-- Trivialization of a restricted global section agrees with ambient evaluation. -/
lemma onOpenIso_globalSection_coordinate (i : ι) (V : X.Opens) (hi : V ≤ U i)
    (s : g.sections ⊤) :
    (g.onOpenIso i V hi).hom.app ⊤
      (g.restrict le_top s) =
      V.topIso.inv (g.evaluate i hi (g.restrict le_top s)) := by
  rw [onOpenIso_hom_app]
  change g.evaluate i ((V.ι_image_le ⊤).trans hi) (g.restrict le_top s) =
    res (V.ι_image_le ⊤) (g.evaluate i hi (g.restrict le_top s))
  rw [← evaluate_restrict, restrict_restrict]

/-- The generator open, restricted to a trivializing chart, is its coordinate basic open. -/
lemma sectionGeneratorOpen_preimage (hU : iSup U = ⊤) (i : ι)
    (V : X.Opens) (hi : V ≤ U i) (s : g.sections ⊤) :
    V.ι ⁻¹ᵁ sectionGeneratorOpen g.sheaf s =
      V.toScheme.basicOpen (V.topIso.inv (g.evaluate i hi (g.restrict le_top s))) := by
  rw [← sectionGeneratorOpen_restrict (g.locallyFreeRankOne hU),
    ← sectionGeneratorOpen_iso (g.onOpenIso i V hi)]
  change sectionGeneratorOpen (structureModule V.toScheme)
    ((g.onOpenIso i V hi).hom.app ⊤ (g.restrict le_top s)) = _
  rw [g.onOpenIso_globalSection_coordinate, sectionGeneratorOpen_structure]

end FLT.Mazur.FCurve.ModuleSheafUnitCocycle.Cocycle
