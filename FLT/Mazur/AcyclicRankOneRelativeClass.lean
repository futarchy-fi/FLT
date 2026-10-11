/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.AcyclicRankOneLineCondition
public import FLT.Mazur.RelativePicardTwistIso

/-!
# The acyclic rank-one condition depends only on the relative Picard class

The line projection formula and residue-fiber trivializations show invariance
under every base-line twist. Thus equality of relative classes transports
the condition, including along arbitrary commuting family squares.
-/

@[expose] public noncomputable section
open CategoryTheory AlgebraicGeometry
namespace FLT.Mazur.CartierAbel
open FCurve SchemePicard
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
attribute [local irreducible] ModuleSheafTensor.tensor
variable {X S : Scheme.{0}} (f : X ⟶ S)

/-- Tensoring by a base line preserves and detects the entire intrinsic condition. -/
theorem acyclicRankOne_baseLineTwist (L : X.Modules) (B : S.Modules)
    (hB : LocallyFreeRankOne B) :
    AcyclicRankOne f (ModuleSheafTensor.tensor L ((Scheme.Modules.pullback f).obj B)) ↔
      AcyclicRankOne f L := by
  refine and_congr (forall_congr' fun s ↦ forall_congr' fun n ↦
    baseLineTwist_fiber_vanishing_iff f L hB s (n + 1)) ?_
  let a := ClosedLineProjectionFormula.projectionIso f L B hB
  exact (show LocallyFreeRankOne _ ↔ LocallyFreeRankOne _ from
    ⟨fun h ↦ h.of_iso a, fun h ↦ h.of_iso a.symm⟩).trans
      (locallyFreeRankOne_tensor_line_iff _ B hB)

/-- Equality of relative Picard classes preserves the actual cohomological condition. -/
theorem acyclicRankOne_relativeClass_iff {L M : X.Modules}
    (hL : LocallyFreeRankOne L) (hM : LocallyFreeRankOne M)
    (hc : relativeClass f (mk L hL) = relativeClass f (mk M hM)) :
    AcyclicRankOne f L ↔ AcyclicRankOne f M := by
  obtain ⟨B, ⟨a⟩⟩ := (relativeClass_mk_eq_iff_twist_iso f hL hM).mp hc
  exact ((acyclicRankOne_iso f a).trans
    (acyclicRankOne_baseLineTwist f L B.val B.property)).symm

/-- The intrinsic condition as a predicate on relative Picard classes. -/
def RelativeAcyclicRankOne (c : RelativePic f) : Prop :=
  ∃ (L : X.Modules) (hL : LocallyFreeRankOne L),
    relativeClass f (mk L hL) = c ∧ AcyclicRankOne f L

/-- Every actual representative detects the relative-class predicate. -/
theorem relativeAcyclicRankOne_mk (L : X.Modules) (hL : LocallyFreeRankOne L) :
    RelativeAcyclicRankOne f (relativeClass f (mk L hL)) ↔ AcyclicRankOne f L := by
  constructor
  · rintro ⟨M, hM, hc, hA⟩
    exact (acyclicRankOne_relativeClass_iff f hM hL hc).mp hA
  · intro hA
    exact ⟨L, hL, rfl, hA⟩

variable {P T : Scheme.{0}} (q : P ⟶ T) (p : P ⟶ X) (g : T ⟶ S)
  (hw : p ≫ f = q ≫ g)

include hw in
/-- Relative-class equality transports the condition on every commuting test family. -/
theorem acyclicRankOne_relativeClass_test_iff {L M : X.Modules}
    (hL : LocallyFreeRankOne L) (hM : LocallyFreeRankOne M)
    (hc : relativeClass f (mk L hL) = relativeClass f (mk M hM)) :
    AcyclicRankOne q ((Scheme.Modules.pullback p).obj L) ↔
      AcyclicRankOne q ((Scheme.Modules.pullback p).obj M) :=
  acyclicRankOne_relativeClass_iff q (hL.pullback p) (hM.pullback p)
    (congrArg (relativeMap q f p g hw.symm) hc)

end FLT.Mazur.CartierAbel
