/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.LocallySplitLineSourceTransport
public import FLT.Mazur.FreeSheafRestrictionCoherence

/-!
# Ordinary restriction of canonical split-line points

The canonical reverse construction commutes with ordinary sheaf restriction,
using the same free restriction comparison as finite free ambient charts.
-/

@[expose] public noncomputable section
open CategoryTheory AlgebraicGeometry
open Scheme.Modules
universe u
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
namespace FLT.Mazur.SplitLineAffinePresentation
open FCurve SplitLineAffineNeighborhood ProjectiveSpace ModuleGlobalEvaluationPullback
variable {X Y : Scheme.{u}} (f : Y ⟶ X) [IsOpenImmersion f]
variable {ι : Type u} [Finite ι] {L : X.Modules}
variable (s : L ⟶ SheafOfModules.free ι)

/-- The original restricted inclusion expressed in canonical free coordinates. -/
def restrictedInclusion : L.restrict f ⟶ SheafOfModules.free ι :=
  (restrictFunctor f).map s ≫ (freeRestrictIso f ι).hom

omit [Finite ι] in
/-- Ordinary and geometric restriction preserve the same original inclusion. -/
lemma restrictedInclusion_comparison :
    (restrictFunctorIsoPullback f).hom.app L ≫ SplitSheafLinePullback.inclusion f s =
      restrictedInclusion f s := by
  dsimp only [restrictedInclusion, SplitSheafLinePullback.inclusion, freeRestrictIso,
    Iso.trans_hom, Iso.app_hom]
  rw [← Category.assoc, ← (restrictFunctorIsoPullback f).hom.naturality,
    Category.assoc]

variable (hL : LocallyFreeRankOne L) (hs : LocallySplit s)

omit [Finite ι] in
include hs in
/-- Actual local splitting persists in the canonical ordinary restriction coordinates. -/
lemma restrictedInclusion_locallySplit : LocallySplit (restrictedInclusion f s) :=
  (hs.restriction s f).postcompose _ (freeRestrictIso f ι)

/-- Ordinary open restriction commutes with the canonical global reverse point. -/
lemma morphism_restriction :
    f ≫ morphism s hL hs =
      morphism (restrictedInclusion f s) (hL.restrict f)
        (restrictedInclusion_locallySplit f s hs) ≫ coefficientMap f.appTop.hom ι := by
  rw [morphism_pullback]
  apply congrArg (· ≫ coefficientMap f.appTop.hom ι)
  exact (morphism_sourceIso ((restrictFunctorIsoPullback f).app L)
    (restrictedInclusion f s) (SplitSheafLinePullback.inclusion f s)
    (restrictedInclusion_comparison f s) (hL.restrict f) (hL.pullback f)
    (restrictedInclusion_locallySplit f s hs) (hs.inclusion f)).symm

end FLT.Mazur.SplitLineAffinePresentation
