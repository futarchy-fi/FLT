/-
Copyright (c) 2026 krandder. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: krandder
-/
module

public import FLT.Mazur.WeierstrassDividedPositiveEqualityAllComponentAction
public import FLT.Mazur.PolygonParameterizedHomExt
import all FLT.Mazur.WeierstrassDividedPositiveEqualityPushout

/-!
# The genuine smooth coefficient action on the whole equality fiber

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
  (hp : 2 * (start + s + 1) = depth)
open WeierstrassIntegralChart
local notation "𝕂" => ResidueField R
local notation "Z" => positiveEqualityCycleComponent hπ data D s hs hstart hk hp
local notation "B" => finiteGlobalCoefficientOverAction hπ data (s + 1) hs 𝕂
local notation "v" => positiveEqualityCyclicSmoothGroupIso D s hk

local notation "p" => pullback.fst (Spec.map (CommRingCat.ofHom (algebraMap R 𝕂)))
  (finiteGlobalStructure hπ data (s + 1) hs)
local notation "C" => Over.mk p
local notation "N" => positiveEqualityCycleNormalization hπ data D s hs hstart hk hp
local notation "Q" => positiveEqualityCycleNodes hπ data D s hs hstart hk
local notation "H" => positiveEqualityCycleCocone_isPushout hπ data D s hs hstart hk hp
local notation "c" => PolygonSplitGroup.component 𝕂 (2 * s + 4) 0
local notation "A" => positiveEqualityCycleAction hπ data D s hs hstart hk hp
local notation "U" => MultiplicativeGroupScheme.gm 𝕂

/-- On the whole original equality fiber the actual smooth action is polygon scaling. -/
theorem positiveEqualityCoefficientAction_eq_cycleAction :
    (v).hom.hom.hom.hom ▷ C ≫ B = c ▷ C ≫ A := by
  let _ : IsSeparated (finiteGlobalStructure hπ data (s + 1) hs) :=
    (finiteGlobalStructure_isProper hπ data (s + 1) hs).toIsSeparated
  let _ : IsSeparated (C).hom := by
    change IsSeparated (pullback.fst _ _)
    infer_instance
  apply PolygonPinching.gm_hom_ext_tori 𝕂 (2 * s + 4) (by omega) N Q H
  intro i
  simp only [positiveEqualityCycleNormalization_ι]
  rw [whiskerLeft_comp_assoc, ← tensorHom_def'_assoc,
    whiskerLeft_comp_assoc, ← tensorHom_def'_assoc,
    positiveEqualityCoefficientAction_component, positiveEqualityCycleAction_component,
    PolygonPinching.rotateIndex_zero]

/-- Every original smooth parameter acts on every point by the same whole-fiber equality. -/
theorem positiveEqualityCoefficientAction_cycle_point
    {T : Over (Spec (.of 𝕂))} (a : T ⟶ U) (b : T ⟶ C) :
    (a ≫ (v).hom.hom.hom.hom) • b = lift (a ≫ c) b ≫ A := by
  have h := congrArg (lift a b ≫ ·)
    (positiveEqualityCoefficientAction_eq_cycleAction hπ data D s hs hstart hk hp)
  simpa only [← Category.assoc, lift_whiskerRight, finiteGlobalCoefficientOverAction_points]
    using h

end FLT.Mazur.WeierstrassDividedDepth
