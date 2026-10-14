/-
Copyright (c) 2026 krandder. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: krandder
-/
module

public import FLT.Mazur.WeierstrassDividedPositiveSplitWholeFiberAction
public import FLT.Mazur.PolygonParameterizedHomExt
import all FLT.Mazur.WeierstrassDividedPositiveSplitPushout

/-!
# The genuine smooth coefficient action on the whole strict fiber

The original pinching pushout detects the action on all component tori.
Thus the proved integral coefficient action is the identity component of the
constructed polygon action on the entire residue fiber, including every node.
-/

@[expose] public noncomputable section
open AlgebraicGeometry CategoryTheory Limits IsLocalRing
open MonoidalCategory CartesianMonoidalCategory
open scoped LaurentPolynomial
namespace FLT.Mazur.WeierstrassDividedDepth
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
universe u
variable {R : Type u} [CommRing R] [IsDomain R] [IsBezout R] [IsLocalRing R]
  {W : WeierstrassCurve R} {π : R} (hπ : π ≠ 0) {start n depth : ℕ}
  (data : (i : Fin (n + 1)) → Data W π (start + i.val))
  (D : SplitNodeDepth W π depth) (s : ℕ) (hs : s + 1 ≤ n)
  (hstart : 0 < start) (hk : 2 * (start + s + 1) ≤ depth)
  (hp : 2 * (start + s + 1) < depth)
open WeierstrassIntegralChart
local notation "𝕂" => ResidueField R
local notation "Z" => positiveSplitCycleComponent hπ data D s hs hstart hk hp
local notation "B" => finiteGlobalCoefficientOverAction hπ data (s + 1) hs 𝕂
local notation "v" => positiveSplitCyclicSmoothGroupIso D s hk

local notation "p" => pullback.fst (Spec.map (CommRingCat.ofHom (algebraMap R 𝕂)))
  (finiteGlobalStructure hπ data (s + 1) hs)
local notation "C" => Over.mk p
local notation "N" => positiveSplitCycleNormalization hπ data D s hs hstart hk hp
local notation "Q" => positiveSplitCycleNodes hπ data D s hs hstart hk hp
local notation "H" => positiveSplitCycleCocone_isPushout hπ data D s hs hstart hk hp
local notation "c" => PolygonSplitGroup.component 𝕂 (2 * s + 5) 0
local notation "A" => positiveSplitCycleAction hπ data D s hs hstart hk hp
local notation "U" => MultiplicativeGroupScheme.gm 𝕂

local notation "J" => positiveSplitOriginalSmoothGroupHom D s hk
local notation "V" => W.map (algebraMap R 𝕂)

/-- The original smooth-group action is the restricted polygon action on the whole fiber. -/
theorem positiveSplitOriginalAction_eq_cycleAction : B = (J).hom.hom.hom ▷ C ≫ A := by
  apply (cancel_epi ((v).hom.hom.hom.hom ▷ C)).mp
  rw [positiveSplitCoefficientAction_eq_cycleAction, ← comp_whiskerRight_assoc,
    positiveSplitCyclicSmoothGroupIso_inclusion]

/-- Every actual smooth parameter acts on every original model point by polygon translation. -/
theorem positiveSplitOriginalAction_cycle_point
    {T : Over (Spec (.of 𝕂))} (a : T ⟶ (integralSmoothGroup V).X) (b : T ⟶ C) :
    a • b = lift (a ≫ (J).hom.hom.hom) b ≫ A := by
  have h := congrArg (lift a b ≫ ·)
    (positiveSplitOriginalAction_eq_cycleAction hπ data D s hs hstart hk hp)
  simpa only [← Category.assoc, lift_whiskerRight, finiteGlobalCoefficientOverAction_points]
    using h

local notation "node" => fun i => finalNodeOverSection hπ data D s hs hk hp
  (positiveSplitCycleNodeIndex start s hstart i)

/-- The actual coefficient action fixes each original node scheme-theoretically. -/
theorem positiveSplitCoefficientAction_node (i : Fin (2 * s + 5)) :
    ((v).hom.hom.hom.hom ⊗ₘ node i) ≫ B = snd U (PolygonPinching.point 𝕂) ≫ node i := by
  rw [tensorHom_def'_assoc,
    positiveSplitCoefficientAction_eq_cycleAction hπ data D s hs hstart hk hp,
    ← tensorHom_def'_assoc, positiveSplitCycleAction_node, PolygonPinching.rotateIndex_zero]

/-- Fixing nodes holds on every test scheme and for every original smooth parameter. -/
theorem positiveSplitOriginalAction_node_point
    {T : Over (Spec (.of 𝕂))} (a : T ⟶ (integralSmoothGroup V).X)
    (b : T ⟶ PolygonPinching.point 𝕂) (i : Fin (2 * s + 5)) :
    a • (b ≫ node i) = b ≫ node i := by
  have h := congrArg (lift (a ≫ (v).inv.hom.hom.hom) b ≫ ·)
    (positiveSplitCoefficientAction_node hπ data D s hs hstart hk hp i)
  rw [← Category.assoc, lift_map, finiteGlobalCoefficientOverAction_points] at h
  have hi : (v).inv.hom.hom.hom ≫ (v).hom.hom.hom.hom = 𝟙 _ :=
    congrArg (fun f => f.hom.hom.hom) (v).inv_hom_id
  simpa only [Category.assoc, lift_snd_assoc, hi, Category.comp_id] using h

end FLT.Mazur.WeierstrassDividedDepth
