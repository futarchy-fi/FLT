/-
Copyright (c) 2026 krandder. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: krandder
-/
module

public import FLT.Mazur.WeierstrassCoefficientShearSuccessiveAction
public import FLT.Mazur.WeierstrassCoefficientShearTorusPair
public import FLT.Mazur.WeierstrassSmoothHorizontalRootParameter

/-!
# The actual torus action on the two successive conic branches

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
  (j : ℕ) (hj : j + 1 ≤ n) (m : ℕ) (hm : j + 1 + m ≤ n)
  (D : SplitNodeDepth W π depth) (hk : 2 * (start + j + 1) < depth)
local notation "K" => ResidueField R
local notation "d" => data (Fin.mk (j + 1) (Nat.lt_succ_of_le hj))
local notation "a" => WeierstrassDilatation.residueTangentUnit D
local notation "hc" => splitDepth_zeroRoot_conditions D
local notation "u" => laurentUnitOverPoint (R := K) (smoothHorizontalTangentUnit D)
local notation "V" => W.map (algebraMap R K)
local notation "I" => rootShearTorusSmoothIso V 0 a (hc).1 (hc).2.1 (hc).2.2.1
  (hc).2.2.2.1 (hc).2.2.2.2
local notation "B" => coefficientShearRetainedTensorChart hπ data K 0
  (j + 1 + m) hm (Fin.mk j (by omega))
local notation "g" => coefficientShearGluedStructure hπ data K 0 (j + 1 + m) hm
local notation "t" => Over.hom (MultiplicativeGroupScheme.gm K)
local notation "i₁" => Spec.map (CommRingCat.ofHom
  (AlgHom.toRingHom (smoothSuccessiveFirstTransportedTensorInput d hπ D hk))) ≫ B
local notation "i₂" => Spec.map (CommRingCat.ofHom
  (AlgHom.toRingHom (smoothSuccessiveSecondTransportedTensorInput d hπ D hk))) ≫ B
local notation "A" => coefficientShearTorusAction hπ data K 0 (j + 1 + m) hm a (hc).1 (hc).2.1
  (hc).2.2.1 (hc).2.2.2.1 (hc).2.2.2.2

/-- The positive tangent unit forms the actual torus-domain pair with the first input. -/
theorem coefficientShearSuccessiveFirst_torusCondition : (u).left ≫ t = i₁ ≫ g := by
  rw [← coefficientShearSuccessiveFirst_condition hπ data j hj m hm D hk 0,
    smoothHorizontalResiduePoint_structure]
  exact (u).w

/-- The same torus parameter pairs with the opposite original tensor input. -/
theorem coefficientShearSuccessiveSecond_torusCondition : (u).left ≫ t = i₂ ≫ g := by
  rw [← coefficientShearSuccessiveSecond_condition hπ data j hj m hm D hk 0,
    smoothHorizontalResiduePoint_structure]
  exact (u).w

/-- The actual torus action is the first independently computed tensor output. -/
theorem coefficientShearTorusAction_successiveFirst :
    pullback.lift (u).left i₁
        (coefficientShearSuccessiveFirst_torusCondition hπ data j hj m hm D hk) ≫ A =
      Spec.map (CommRingCat.ofHom
        (AlgHom.toRingHom (smoothSuccessiveFirstTensorOutput d hπ D hk))) ≫ B := by
  have hp : (u).left ≫ (I).hom = smoothHorizontalResiduePoint D D.depth_pos :=
    smoothHorizontalResiduePoint_rootParameter D
  rw [coefficientShearTorusAction_pair]
  simp only [hp]
  exact coefficientShearSuccessiveFirst_action hπ data j hj m hm D hk 0

/-- The actual torus action is the opposite independently computed tensor output. -/
theorem coefficientShearTorusAction_successiveSecond :
    pullback.lift (u).left i₂
        (coefficientShearSuccessiveSecond_torusCondition hπ data j hj m hm D hk) ≫ A =
      Spec.map (CommRingCat.ofHom
        (AlgHom.toRingHom (smoothSuccessiveSecondTensorOutput d hπ D hk))) ≫ B := by
  have hp : (u).left ≫ (I).hom = smoothHorizontalResiduePoint D D.depth_pos :=
    smoothHorizontalResiduePoint_rootParameter D
  rw [coefficientShearTorusAction_pair]
  simp only [hp]
  exact coefficientShearSuccessiveSecond_action hπ data j hj m hm D hk 0

end FLT.Mazur.WeierstrassDividedDepth
