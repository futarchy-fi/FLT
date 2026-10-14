/-
Copyright (c) 2026 krandder. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: krandder
-/
module

public import FLT.Mazur.WeierstrassDividedPositiveSplitReflection
public import FLT.Mazur.WeierstrassDividedPositiveSplitWholeFiberAction
public import FLT.Mazur.NeronPolygonReflectionAction
import all FLT.Mazur.WeierstrassDividedPositiveSplitCyclicTorusAction
import all FLT.Mazur.WeierstrassDividedPositiveSplitSmoothGroup
import all FLT.Mazur.WeierstrassDividedPositiveSplitPushout

/-!
# Reflection of the actual specialized action on the entire residue fiber

The full pinching reflection inverts the split group parameter. The existing
whole-fiber comparison gives the same equation for the original integral action.
-/

@[expose] public noncomputable section
open AlgebraicGeometry CategoryTheory Limits IsLocalRing
open MonoidalCategory CartesianMonoidalCategory MonObj GrpObj
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
local notation "K" => ResidueField R
local notation "p" => pullback.fst (Spec.map (CommRingCat.ofHom (algebraMap R K)))
  (finiteGlobalStructure hπ data (s + 1) hs)
local notation "Z" => positiveSplitCycleComponent hπ data D s hs hstart hk hp
local notation "N" => positiveSplitCycleNormalization hπ data D s hs hstart hk hp
local notation "Q" => positiveSplitCycleNodes hπ data D s hs hstart hk hp
local notation "H" => positiveSplitCycleCocone_isPushout hπ data D s hs hstart hk hp
local notation "ρ" => Iso.hom (ProjectiveLine.endpointReversalOverIso K)

local notation "σ" => positiveSplitReflection hπ data D s hs hstart hk hp
local notation "A" => positiveSplitCycleAction hπ data D s hs hstart hk hp
local notation "C" => Over.mk p
local notation "G" => PolygonSplitGroup.model K (2 * s + 5)
local notation "U" => MultiplicativeGroupScheme.gm K
local notation "v" => positiveSplitCyclicSmoothGroupIso D s hk
local notation "B" => finiteGlobalCoefficientOverAction hπ data (s + 1) hs K
local notation "c" => PolygonSplitGroup.component K (2 * s + 5) 0

/-- Reflection inverts the full split-group action on every point of the original model. -/
@[reassoc] theorem positiveSplitReflection_cycleAction :
    A ≫ σ = (PolygonSplitGroup.inversion K (2 * s + 5) ⊗ₘ σ) ≫ A :=
  PolygonPinching.polygonAction_reflection K (by omega) N Q H

/-- The actual specialized integral action has inverse-parameter reflection on the whole fiber. -/
theorem positiveSplitReflection_coefficientAction :
    (v).hom.hom.hom.hom ▷ C ≫ B ≫ σ =
      (ι[U] ⊗ₘ σ) ≫ (v).hom.hom.hom.hom ▷ C ≫ B := by
  rw [← Category.assoc,
    positiveSplitCoefficientAction_eq_cycleAction hπ data D s hs hstart hk hp,
    Category.assoc, positiveSplitReflection_cycleAction]
  rw [whiskerRight_comp_tensorHom_assoc, PolygonSplitGroup.component_inversion, neg_zero]
  rw [← tensorHom_comp_whiskerRight_assoc]

/-- Universal test-scheme points retain the actual action, even at singular model points. -/
theorem positiveSplitReflection_coefficientPoint
    {T : Over (Spec (.of K))} (a : T ⟶ U) (b : T ⟶ C) :
    ((a ≫ (v).hom.hom.hom.hom) • b) ≫ σ =
      ((a ≫ ι[U]) ≫ (v).hom.hom.hom.hom) • (b ≫ σ) := by
  have hEq := congrArg (lift a b ≫ ·)
    (positiveSplitReflection_coefficientAction hπ data D s hs hstart hk hp)
  simpa only [← Category.assoc, lift_whiskerRight, lift_map,
    finiteGlobalCoefficientOverAction_points] using hEq

/-- Applying reflection on both sides conjugates the original action to inverse parameter. -/
theorem positiveSplitReflection_conjugateCoefficientAction :
    U ◁ σ ≫ (v).hom.hom.hom.hom ▷ C ≫ B ≫ σ =
      ι[U] ▷ C ≫ (v).hom.hom.hom.hom ▷ C ≫ B := by
  rw [positiveSplitReflection_coefficientAction,
    whiskerLeft_comp_tensorHom_assoc, positiveSplitReflection_involutive, tensorHom_id]

end FLT.Mazur.WeierstrassDividedDepth
