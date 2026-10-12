/-
Copyright (c) 2026 krandder. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: krandder
-/
module

public import FLT.Mazur.WeierstrassCoefficientShearHorizontalAction
public import FLT.Mazur.WeierstrassCoefficientShearTorusPair
public import FLT.Mazur.WeierstrassSmoothHorizontalRootParameter

/-!
# The actual torus action on the two horizontal conic branches

The positive tangent unit supplies the genuine torus-domain input. The
output remains the independently constructed original tensor action on each branch.
-/

@[expose] public noncomputable section
open AlgebraicGeometry CategoryTheory Limits IsLocalRing
namespace FLT.Mazur.WeierstrassDividedDepth
open WeierstrassIntegralChart
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
variable {R : Type} [CommRing R] [IsDomain R] [IsBezout R] [IsLocalRing R]
  {W : WeierstrassCurve R} {π : R} (hπ : π ≠ 0) {start n depth : ℕ}
  (data : (i : Fin (n + 1)) → Data W π (start + i.val))
  (D : SplitNodeDepth W π depth) (hstart : 0 < start) (hk : 2 * start < depth)
  (j : ℕ) (hj : j ≤ n)
local notation "K" => ResidueField R
local notation "d" => data (Fin.mk 0 (Nat.zero_lt_succ n))
local notation "a" => WeierstrassDilatation.residueTangentUnit D
local notation "hc" => splitDepth_zeroRoot_conditions D
local notation "u" => laurentUnitOverPoint (R := K) (smoothHorizontalTangentUnit D)
local notation "V" => W.map (algebraMap R K)
local notation "I" => rootShearTorusSmoothIso V 0 a (hc).1 (hc).2.1 (hc).2.2.1
  (hc).2.2.2.1 (hc).2.2.2.2
local notation "B" => coefficientShearInitialTensorChart hπ data K 0 j hj
local notation "g" => coefficientShearGluedStructure hπ data K 0 j hj
local notation "t" => Over.hom (MultiplicativeGroupScheme.gm K)
local notation "i₁" => Spec.map (CommRingCat.ofHom
  (AlgHom.toRingHom (smoothHorizontalFirstTensorInput D d hstart hk))) ≫ B
local notation "i₂" => Spec.map (CommRingCat.ofHom
  (AlgHom.toRingHom (smoothHorizontalSecondTensorInput D d hstart hk))) ≫ B
local notation "A" => coefficientShearTorusAction hπ data K 0 j hj a (hc).1 (hc).2.1
  (hc).2.2.1 (hc).2.2.2.1 (hc).2.2.2.2

/-- The positive tangent unit forms the actual torus-domain pair with the first input. -/
theorem coefficientShearHorizontalFirst_torusCondition : (u).left ≫ t = i₁ ≫ g := by
  rw [← coefficientShearHorizontalFirst_condition hπ data D hstart hk 0 j hj,
    smoothHorizontalResiduePoint_structure]
  exact (u).w

/-- The same torus parameter pairs with the opposite original tensor input. -/
theorem coefficientShearHorizontalSecond_torusCondition : (u).left ≫ t = i₂ ≫ g := by
  rw [← coefficientShearHorizontalSecond_condition hπ data D hstart hk 0 j hj,
    smoothHorizontalResiduePoint_structure]
  exact (u).w

/-- The actual torus action is the first independently computed tensor output. -/
theorem coefficientShearTorusAction_horizontalFirst :
    pullback.lift (u).left i₁
        (coefficientShearHorizontalFirst_torusCondition hπ data D hstart hk j hj) ≫ A =
      Spec.map (CommRingCat.ofHom
        (AlgHom.toRingHom (smoothHorizontalFirstTensorAction D d hstart hk hπ))) ≫ B := by
  have hp : (u).left ≫ (I).hom = smoothHorizontalResiduePoint D D.depth_pos :=
    smoothHorizontalResiduePoint_rootParameter D
  rw [coefficientShearTorusAction_pair]
  simp only [hp]
  exact coefficientShearHorizontalFirst_action hπ data D hstart hk 0 j hj

/-- The actual torus action is the opposite independently computed tensor output. -/
theorem coefficientShearTorusAction_horizontalSecond :
    pullback.lift (u).left i₂
        (coefficientShearHorizontalSecond_torusCondition hπ data D hstart hk j hj) ≫ A =
      Spec.map (CommRingCat.ofHom
        (AlgHom.toRingHom (smoothHorizontalSecondTensorAction D d hstart hk hπ))) ≫ B := by
  have hp : (u).left ≫ (I).hom = smoothHorizontalResiduePoint D D.depth_pos :=
    smoothHorizontalResiduePoint_rootParameter D
  rw [coefficientShearTorusAction_pair]
  simp only [hp]
  exact coefficientShearHorizontalSecond_action hπ data D hstart hk 0 j hj

end FLT.Mazur.WeierstrassDividedDepth
