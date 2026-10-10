/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.DualAtlasSectionForwardReverse
public import FLT.Mazur.LocallySplitSheafMonomorphism

/-!
# Geometric pullback of recovered ambient line inclusions

Reconstruction of an actual pulled line compares canonically with pullback
of its reconstruction, inside the pulled ambient sheaf. The comparison
preserves the inclusion and commutes with the global inverse isomorphisms.
This does not construct a base-change morphism of the projective atlases.
-/

@[expose] public noncomputable section
open CategoryTheory AlgebraicGeometry
open Scheme.Modules
universe u
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
attribute [local irreducible] FLT.Mazur.CoherentSubmoduleGluing.data
  FLT.Mazur.LocallySplitLineAtlasSection.morphism
namespace FLT.Mazur.LineRecoveryPullback
open FCurve SplitLineAffineNeighborhood LocallySplitLineAtlasSection
variable {X T : Scheme.{u}} {L M : X.Modules} (s : L ⟶ M) [Mono s]
variable (hL : LocallyFreeRankOne L) (hs : LocallySplit s) (hM : LocallyFiniteFree M)
variable (f : T ⟶ X)

/-- Actual geometric reconstruction commutes with pullback through the original source line. -/
def comparison :
    recoveredLine ((pullback f).map s) (hL.pullback f) (hs.pullback s f) (hM.pullback f) ≅
      (pullback f).obj (recoveredLine s hL hs hM) := by
  let _ := hs.pullback_mono s f
  exact forwardReverseIso ((pullback f).map s) (hL.pullback f) (hs.pullback s f) (hM.pullback f) ≪≫
    ((pullback f).mapIso (forwardReverseIso s hL hs hM)).symm

/-- The comparison commutes with both actual global inverse isomorphisms. -/
lemma comparison_inverse :
    let _ := hs.pullback_mono s f
    (comparison s hL hs hM f).hom ≫ (pullback f).map (forwardReverseIso s hL hs hM).hom =
      (forwardReverseIso ((pullback f).map s)
        (hL.pullback f) (hs.pullback s f) (hM.pullback f)).hom := by
  let _ := hs.pullback_mono s f
  simp only [comparison, Iso.trans_hom, Iso.symm_hom, Functor.mapIso_inv,
    Category.assoc, ← Functor.map_comp, Iso.inv_hom_id, CategoryTheory.Functor.map_id,
    Category.comp_id]

/-- Reconstruction preserves the original inclusion in the genuinely pulled ambient sheaf. -/
lemma comparison_inclusion :
    (comparison s hL hs hM f).hom ≫ (pullback f).map (recoveredInclusion s hL hs hM) =
      recoveredInclusion ((pullback f).map s)
        (hL.pullback f) (hs.pullback s f) (hM.pullback f) := by
  let _ := hs.pullback_mono s f
  rw [← forwardReverseIso_inclusion s hL hs hM, Functor.map_comp,
    ← Category.assoc, comparison_inverse, forwardReverseIso_inclusion]

/-- The original ambient inclusion determines the geometric comparison uniquely. -/
lemma comparison_unique
    (a : recoveredLine ((pullback f).map s)
        (hL.pullback f) (hs.pullback s f) (hM.pullback f) ⟶
      (pullback f).obj (recoveredLine s hL hs hM))
    (ha : a ≫ (pullback f).map (recoveredInclusion s hL hs hM) =
      recoveredInclusion ((pullback f).map s)
        (hL.pullback f) (hs.pullback s f) (hM.pullback f)) :
    a = (comparison s hL hs hM f).hom := by
  let _ := DualAtlasSectionForwardLine.pullback_mono M hM
    (morphism s hL hs hM) (morphism_projection s hL hs hM) f
  apply (cancel_mono ((pullback f).map (recoveredInclusion s hL hs hM))).mp
  rw [ha, comparison_inclusion]

end FLT.Mazur.LineRecoveryPullback
