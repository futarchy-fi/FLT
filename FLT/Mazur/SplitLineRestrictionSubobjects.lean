/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.LocallySplitLineOpenRestriction
public import FLT.Mazur.ModuleSubobjectCoverEquality

/-!
# Reflecting equality of actual free-coordinate pullback subobjects

The canonical restriction comparisons preserve the original ambient
subobjects. Equality after open pullback therefore implies equality of
ordinary restrictions, which can be checked on an open cover.
-/

@[expose] public noncomputable section
open CategoryTheory AlgebraicGeometry
open Scheme.Modules
universe u
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
namespace FLT.Mazur.SplitLineAffinePresentation
open ModuleGlobalEvaluationPullback
variable {X Y : Scheme.{u}} (f : Y ⟶ X) [IsOpenImmersion f]
variable {ι : Type u} {L N : X.Modules}
variable (s : L ⟶ SheafOfModules.free ι) (t : N ⟶ SheafOfModules.free ι)
variable [Mono s] [Mono t]
variable [Mono (SplitSheafLinePullback.inclusion f s)]
variable [Mono (SplitSheafLinePullback.inclusion f t)]

/-- Open pullback equality in free coordinates reflects equality of original restrictions. -/
lemma restriction_subobject_eq_of_pullback
    (h : Subobject.mk (SplitSheafLinePullback.inclusion f s) =
      Subobject.mk (SplitSheafLinePullback.inclusion f t)) :
    Subobject.mk ((restrictFunctor f).map s) =
      Subobject.mk ((restrictFunctor f).map t) := by
  let _ : Mono (restrictedInclusion f s) := by
    dsimp only [restrictedInclusion]
    infer_instance
  let _ : Mono (restrictedInclusion f t) := by
    dsimp only [restrictedInclusion]
    infer_instance
  apply Subobject.map_obj_injective (freeRestrictIso f ι).hom
  change Subobject.mk (restrictedInclusion f s) = Subobject.mk (restrictedInclusion f t)
  have hs : Subobject.mk (restrictedInclusion f s) =
      Subobject.mk (SplitSheafLinePullback.inclusion f s) :=
    Subobject.mk_eq_mk_of_comm _ _ ((restrictFunctorIsoPullback f).app L)
      (restrictedInclusion_comparison f s)
  have ht : Subobject.mk (restrictedInclusion f t) =
      Subobject.mk (SplitSheafLinePullback.inclusion f t) :=
    Subobject.mk_eq_mk_of_comm _ _ ((restrictFunctorIsoPullback f).app N)
      (restrictedInclusion_comparison f t)
  exact hs.trans (h.trans ht.symm)

end FLT.Mazur.SplitLineAffinePresentation
