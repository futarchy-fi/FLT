/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.PolygonCompleteClosedActionRotation
public import FLT.Mazur.PolygonCompleteClosedCyclicGroup
public import FLT.Mazur.ConstantCyclicActionDescent

/-!
# The entire complete cyclic action on the original boundary

The constant cyclic scheme action on the original closed square is the
restriction of the polygon's full smooth-group action along the actual
all-one subgroup. The equality holds on whole schemes in all characteristics.
-/

@[expose] public noncomputable section
open CategoryTheory Limits AlgebraicGeometry MonoidalCategory MonObj
namespace FLT.Mazur.PolygonInfinitesimalStages
open PolygonPinching
set_option backward.isDefEq.respectTransparency false
attribute [local irreducible] exactVeroneseProj exactVeroneseProjToBase completeRotation
variable (K : Type) [Field K] (n : ℕ) (h : 2 ≤ n) [NeZero n]
local notation "C" => PolygonCyclicAtlas.polygon K n h
local notation "P" => PolygonCyclicAtlas.normalization K n h
local notation "Q" => PolygonCyclicAtlas.nodes K n h
local notation "hn" => (Nat.lt_of_lt_of_le (Nat.succ_pos 1) h)
local notation "hp" => PolygonCyclicPushout.isPushout K n h hn
local notation "b" => completeClosedBase K
local notation "j" => completeClosedFiberInclusion K n h
local notation "q" => PolygonCyclicAtlas.toBase K n h
local notation "hb" => completeClosedFiber_isPullback K n h

omit [NeZero n] in
/-- The original unit-one point is exactly the finite cyclic inclusion's component. -/
theorem completeClosedGroupPoint_eq (a : ZMod n) :
    PolygonActionTranslation.groupPoint K n 1 a =
      η[MultiplicativeGroupScheme.gm K] ≫ PolygonSplitGroup.component K n a := by
  unfold PolygonActionTranslation.groupPoint
  congr 1
  apply Over.OverMorphism.ext
  exact (ProjectiveLineActionSpecialization.identity_left K).symm

/-- The full scheme action on the original boundary is restriction along its actual subgroup. -/
theorem completeCyclicAction_closed_eq :
    completeCyclicAction K n h b j q hb =
      ConstantCyclicInclusion.inclusion K n ▷ C ≫ PolygonUniversalAction.act K n hn P Q hp := by
  symm
  apply ConstantCyclicSchemeAction.act_unique
  intro a
  rw [← comp_whiskerRight_assoc, ConstantCyclicInclusion.component_inclusion,
    ← completeClosedGroupPoint_eq]
  have he := congrArg (fun f : C ⟶ C ↦ (λ_ C).hom ≫ f)
    (completeCartesianRotationOver_closed_translation K n h a).symm
  simpa only [PolygonActionTranslation.translation, Category.assoc,
    Iso.hom_inv_id_assoc] using he

end FLT.Mazur.PolygonInfinitesimalStages
