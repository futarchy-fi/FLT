/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.LocallySplitLinePointRecovery
public import FLT.Mazur.LocallySplitLineAtlasChartRecovery
public import FLT.Mazur.DualAtlasSectionForwardLine

/-!
# Forward after reverse for actual ambient line subobjects

The normalized chart points recover the original restricted inclusions.
Descent gives equality of the global ambient subobjects and a canonical
isomorphism of their source sheaves preserving the original inclusion.
-/

@[expose] public noncomputable section
open CategoryTheory AlgebraicGeometry
open Scheme.Modules
universe u
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
attribute [local irreducible] FLT.Mazur.CoherentSubmoduleGluing.data
  FLT.Mazur.LocallySplitLineAmbientChart.point
  FLT.Mazur.LocallySplitLineAtlasSection.morphism
  FLT.Mazur.FiniteFreeChartTransitions.refineChart
namespace FLT.Mazur.LocallySplitLineAtlasSection
open FCurve SplitLineAffineNeighborhood DualAtlasSectionLineCover
open FiniteFreeChartTransitions AffineFreeSheafCoordinates
variable {X : Scheme.{u}} {L M : X.Modules} (s : L ⟶ M) [Mono s]
variable (hL : LocallyFreeRankOne L) (hs : LocallySplit s) (hM : LocallyFiniteFree M)

/-- The forward line associated to the original inclusion's actual reverse section. -/
abbrev recoveredLine : X.Modules := DualAtlasSectionForwardLine.line M hM
  (morphism s hL hs hM) (morphism_projection s hL hs hM)

/-- Its actual recovered inclusion in the original ambient sheaf. -/
abbrev recoveredInclusion : recoveredLine s hL hs hM ⟶ M :=
  DualAtlasSectionForwardLine.inclusion M hM
    (morphism s hL hs hM) (morphism_projection s hL hs hM)

/-- The actual recovered normalized inclusion is the original subobject on each neighborhood. -/
lemma neighborhood_subobject (n : Neighborhood M hM (morphism s hL hs hM)
    (morphism_projection s hL hs hM)) :
    Subobject.mk ((restrictFunctor n.opens.ι).map s) =
      Subobject.mk (chartSectionLineInclusion M le_rfl (frame n) n.coordinate n.line) := by
  let e := refineChart M le_rfl (frame n)
  let t := LocallySplitLineAmbientChart.inclusion s n.opens e
  let _ : Mono t := by
    dsimp only [t, LocallySplitLineAmbientChart.inclusion]
    infer_instance
  have hp : LocallySplitLineAmbientChart.point s hL hs n.opens e =
      ProjectiveSpace.affineSectionLinePoint (.id _) n.coordinate n.line :=
    (LocallySplitLineAmbientChart.point_refine_self s hL hs n.opens (frame n)).trans
      (neighborhood_point s hL hs hM n)
  unfold LocallySplitLineAmbientChart.point at hp
  have he := SplitLineAffinePresentation.subobject_eq_sectionLine t (hL.restrict n.opens.ι)
    (LocallySplitLineAmbientChart.inclusion_locallySplit s hs n.opens e)
    n.coordinate n.line hp
  apply Subobject.map_obj_injective e.hom
  change Subobject.mk t = Subobject.mk
    (chartSectionLineInclusion M le_rfl (frame n) n.coordinate n.line ≫ e.hom)
  have hc : chartSectionLineInclusion M le_rfl (frame n) n.coordinate n.line ≫ e.hom =
      sectionLineInclusion n.opens.toScheme n.coordinate n.line := by
    simp only [chartSectionLineInclusion, e, Category.assoc,
      Iso.inv_hom_id, Category.comp_id]
  simpa only [hc] using he

/-- Forward after reverse recovers the original global ambient line subobject. -/
theorem forward_reverse_subobject :
    Subobject.mk (recoveredInclusion s hL hs hM) = Subobject.mk s := by
  symm
  exact AffineSectionLineGluing.subobject_unique
    (DualAtlasSectionForwardLine.compatible M hM
      (morphism s hL hs hM) (morphism_projection s hL hs hM))
    (iSup_opens M hM (morphism s hL hs hM) (morphism_projection s hL hs hM)) s
    (neighborhood_subobject s hL hs hM)

/-- The global inverse comparison identifies the actual original source line. -/
def forwardReverseIso : recoveredLine s hL hs hM ≅ L :=
  Subobject.isoOfMkEqMk _ s (forward_reverse_subobject s hL hs hM)

/-- The canonical inverse comparison retains the original ambient inclusion. -/
lemma forwardReverseIso_inclusion :
    (forwardReverseIso s hL hs hM).hom ≫ s = recoveredInclusion s hL hs hM := by
  simp only [forwardReverseIso, Subobject.isoOfMkEqMk_hom, Subobject.ofMkLEMk_comp]

/-- The original inclusion uniquely determines the global inverse comparison. -/
lemma forwardReverseIso_unique (a : recoveredLine s hL hs hM ⟶ L)
    (ha : a ≫ s = recoveredInclusion s hL hs hM) : a = (forwardReverseIso s hL hs hM).hom := by
  apply (cancel_mono s).mp
  rw [ha, forwardReverseIso_inclusion]

end FLT.Mazur.LocallySplitLineAtlasSection
