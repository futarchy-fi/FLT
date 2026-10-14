/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.PolygonCompleteClosedCyclicGroup
public import FLT.Mazur.PolygonFiniteSubgroup

/-!
# The original complete divisor as a finite subgroup on the closed polygon

The carrier is the actual pulled-back complete product ideal, with its
transported commutative group law. Its map to the full polygon group retains
exactly the original closed embedding and its scheme-theoretic degree.
-/

@[expose] public noncomputable section
open CategoryTheory Limits AlgebraicGeometry MonoidalCategory
namespace FLT.Mazur.PolygonInfinitesimalStages
open PolygonPinching GeneralizedEllipticCurve
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
attribute [local irreducible] exactVeroneseProj exactVeroneseProjToBase
attribute [local instance] completeClosedPolygon_lfp cyclic_lfp
variable (K : Type) [Field K] (n : ℕ) (h : 2 ≤ n) [NeZero n]
local notation "P" => PolygonCyclicAtlas.normalization K n h
local notation "Q" => PolygonCyclicAtlas.nodes K n h
local notation "hn" => (Nat.lt_of_lt_of_le (Nat.succ_pos 1) h)
local notation "hp" => PolygonCyclicPushout.isPushout K n h hn
local notation "b" => completeClosedBase K
local notation "j" => completeClosedFiberInclusion K n h
local notation "q" => PolygonCyclicAtlas.toBase K n h
local notation "hb" => completeClosedFiber_isPullback K n h

/-- The actual complete divisor embeds in the full split closed group. -/
def completeClosedSubgroupInclusion :
    completeCyclicDivisor K n h j q ⟶ PolygonSplitGroup.model K n :=
  (completeCyclicDivisorIso K n h b j q hb).inv ≫ ConstantCyclicInclusion.inclusion K n

/-- Passing to the actual smooth open recovers the complete divisor's smooth inclusion. -/
theorem completeClosedSubgroupInclusion_smoothIso :
    completeClosedSubgroupInclusion K n h ≫ (smoothIso K n hn P Q hp).inv =
      completeCyclicDivisorSmoothMap K n h b j q hb := by
  rw [completeClosedSubgroupInclusion, Category.assoc,
    ← completeSmoothCyclicMarking_closed_eq]
  rfl

/-- The full-group inclusion retains the original complete closed-divisor embedding. -/
@[reassoc] theorem completeClosedSubgroupInclusion_curve :
    (completeClosedSubgroupInclusion K n h).left ≫
      (PolygonActionSmooth.smoothMap K n hn P Q hp).left =
        ((completeMarkingDivisor K n h).comap j).subschemeι := by
  change (completeClosedSubgroupInclusion K n h).left ≫
    (smoothIso K n hn P Q hp).inv.left ≫ (q).smoothLocus.ι = _
  rw [← Category.assoc, ← Over.comp_left, completeClosedSubgroupInclusion_smoothIso]
  exact completeCyclicDivisorSmoothMap_ι K n h b j q hb

/-- The complete product divisor is a rank-n subgroup of the original closed DR curve. -/
def completeClosedFiniteSubgroup :
    (PolygonGeneralizedCurve.curve K n hn P Q hp).FiniteSubgroup n := by
  let _ := completeCyclicDivisorCommGrpObj K n h b j q hb
  refine
    { carrier := completeCyclicDivisor K n h j q
      inclusion := completeClosedSubgroupInclusion K n h
      isMonHom := ?_
      closed := ?_
      degree := completeCyclicDivisor_degree K n h b j q hb }
  · dsimp only [completeClosedSubgroupInclusion]
    infer_instance
  · have : IsOpenImmersion (PolygonActionSmooth.smoothMap K n hn P Q hp).left := by
      dsimp only [PolygonActionSmooth.smoothMap, PolygonActionSmooth.smoothι,
        Over.comp_left, Over.homMk_left]
      have : IsIso (smoothIso K n hn P Q hp).inv.left :=
        inferInstanceAs (IsIso ((Over.forget _).map (smoothIso K n hn P Q hp).inv))
      infer_instance
    have : IsClosedImmersion ((completeClosedSubgroupInclusion K n h).left ≫
        (PolygonActionSmooth.smoothMap K n hn P Q hp).left) := by
      rw [completeClosedSubgroupInclusion_curve]
      infer_instance
    exact IsClosedImmersion.of_comp _ (PolygonActionSmooth.smoothMap K n hn P Q hp).left

/-- The whole-curve map is the exact original pulled-back product-divisor inclusion. -/
@[simp] theorem completeClosedFiniteSubgroup_curveMap :
    (completeClosedFiniteSubgroup K n h).curveMap.left =
      ((completeMarkingDivisor K n h).comap j).subschemeι :=
  completeClosedSubgroupInclusion_curve K n h

/-- The finite subgroup retains the original complete product ideal. -/
@[simp] theorem completeClosedFiniteSubgroup_ideal :
    (completeClosedFiniteSubgroup K n h).ideal = (completeMarkingDivisor K n h).comap j := by
  rw [FiniteSubgroup.ideal, completeClosedFiniteSubgroup_curveMap,
    Scheme.IdealSheafData.ker_subschemeι]

end FLT.Mazur.PolygonInfinitesimalStages
