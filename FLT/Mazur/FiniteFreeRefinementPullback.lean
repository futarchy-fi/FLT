/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.FiniteFreeChartSelfRefinement
public import FLT.Mazur.FiniteFreeFrameRestrictionSquare
public import FLT.Mazur.FramedDualProjectivePullback

/-!
# Original dual refinements as geometric pullback maps

The existing dual chart inclusion is the framed projective map for the actual
comparison between restriction to the smaller open and pullback from the larger.
-/

@[expose] public noncomputable section
open CategoryTheory AlgebraicGeometry
open Scheme.Modules
universe u
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
namespace FLT.Mazur.FiniteFreeChartTransitions
open FiniteFreePullbackFrame OpenModuleRestrictionCoherence DualFreeSheafCoordinates
variable {X : Scheme.{u}} (M : X.Modules)

/-- Compare the original smaller restriction with the pullback from the larger open. -/
def refinementPullbackIso {U V : X.Opens} (h : U ≤ V) :
    M.restrict U.ι ≅ (pullback (X.homOfLE h)).obj (M.restrict V.ι) :=
  nested M h ≪≫ (restrictFunctorIsoPullback (X.homOfLE h)).app _

/-- The original refined frame is its genuine geometric pullback in this comparison. -/
lemma refineChart_pullback {U V : X.Opens} (h : U ≤ V) {ι : Type u}
    (e : M.restrict V.ι ≅ SheafOfModules.free ι) :
    refineChart M h e = refinementPullbackIso M h ≪≫ frame (X.homOfLE h) e := by
  change nested M h ≪≫ restrictFrame (X.homOfLE h) e = _
  rw [restrictFrame_eq]
  rfl

/-- Refining two frames pulls back their actual coordinate change. -/
lemma refineChart_change {U V : X.Opens} (h : U ≤ V) {ι κ : Type u}
    (e : M.restrict V.ι ≅ SheafOfModules.free ι)
    (d : M.restrict V.ι ≅ SheafOfModules.free κ) :
    (refineChart M h e).symm ≪≫ refineChart M h d =
      AffineFreeSheafCoordinates.pullbackFreeIso (X.homOfLE h) (e.symm ≪≫ d) := by
  rw [refineChart_pullback, refineChart_pullback, ← change_frame]
  apply Iso.ext
  simp

/-- The original dual transition is exactly the constructed geometric framed morphism. -/
lemma dualChartInclusion_eq_map {U V : X.Opens} [IsAffine U.toScheme]
    (h : U ≤ V) {ι κ : Type u} [Finite ι] [Finite κ]
    (e : M.restrict U.ι ≅ SheafOfModules.free ι)
    (d : M.restrict V.ι ≅ SheafOfModules.free κ) :
    dualChartInclusion M h e d = FramedDualProjectivePullback.map (X.homOfLE h) d
      ((refinementPullbackIso M h).symm ≪≫ e) := by
  have ht : transition M le_rfl h e d =
      ((refinementPullbackIso M h).symm ≪≫ e).symm ≪≫ frame (X.homOfLE h) d := by
    rw [transition, refineChart_self, refineChart_pullback]
    rfl
  change (projectiveIso (transition M le_rfl h e d)).hom ≫ _ = _
  rw [ht]
  rfl

end FLT.Mazur.FiniteFreeChartTransitions
