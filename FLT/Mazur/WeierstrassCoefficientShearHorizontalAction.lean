/-
Copyright (c) 2026 krandder. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: krandder
-/
module

public import FLT.Mazur.WeierstrassCoefficientShearInitialSmooth
public import FLT.Mazur.WeierstrassCoefficientShearSmoothOrbit
public import FLT.Mazur.WeierstrassDividedHorizontalCoefficientPointAction

/-!
# The actual sheared action on both original horizontal conic inputs

The independently constructed tensor outputs reconstruct the original
coefficient action. Both statements retain the complete tensor embeddings.
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
  (r : ResidueField R) (j : ℕ) (hj : j ≤ n)
local notation "K" => ResidueField R
local notation "d" => data (Fin.mk 0 (Nat.zero_lt_succ n))
local notation "a" => smoothHorizontalResiduePoint D D.depth_pos
local notation "V" => W.map (algebraMap R K)
local notation "B" => coefficientShearInitialTensorChart hπ data K r j hj
local notation "E" => coefficientShearGluedIso hπ data K r j hj
local notation "g" => coefficientShearGluedStructure hπ data K r j hj
local notation "i₁" => Spec.map (CommRingCat.ofHom
  (AlgHom.toRingHom (smoothHorizontalFirstTensorInput D d hstart hk))) ≫ B
local notation "i₂" => Spec.map (CommRingCat.ofHom
  (AlgHom.toRingHom (smoothHorizontalSecondTensorInput D d hstart hk))) ≫ B
local notation "o₁" => Spec.map (CommRingCat.ofHom
  (AlgHom.toRingHom (smoothHorizontalFirstTensorAction D d hstart hk hπ))) ≫ B
local notation "o₂" => Spec.map (CommRingCat.ofHom
  (AlgHom.toRingHom (smoothHorizontalSecondTensorAction D d hstart hk hπ))) ≫ B

/-- The first original conic input lies in the actual smooth action domain. -/
theorem coefficientShearHorizontalFirst_condition :
    a ≫ integralSmoothStructure V = i₁ ≫ g := by
  simp only [coefficientShearGluedStructure, Category.assoc,
    coefficientShearInitialTensorChart_original_assoc]
  exact finiteHorizontalFirstCoefficientInput_condition hπ data D hstart hk j hj

/-- The second original conic input lies in the actual smooth action domain. -/
theorem coefficientShearHorizontalSecond_condition :
    a ≫ integralSmoothStructure V = i₂ ≫ g := by
  simp only [coefficientShearGluedStructure, Category.assoc,
    coefficientShearInitialTensorChart_original_assoc]
  exact finiteHorizontalSecondCoefficientInput_condition hπ data D hstart hk j hj

/-- The genuine smooth action equals the independently calculated first tensor output. -/
theorem coefficientShearHorizontalFirst_action :
    pullback.lift a i₁
        (coefficientShearHorizontalFirst_condition hπ data D hstart hk r j hj) ≫
      coefficientShearAction hπ data K r j hj = o₁ := by
  apply (cancel_mono (E).hom).mp
  rw [coefficientShearAction_pair]
  simp only [Category.assoc, Iso.inv_hom_id, Category.comp_id,
    coefficientShearInitialTensorChart_original]
  exact (finiteHorizontalFirstTensorAction_coefficient hπ data D hstart hk j hj).symm

/-- The genuine smooth action equals the independently calculated opposite tensor output. -/
theorem coefficientShearHorizontalSecond_action :
    pullback.lift a i₂
        (coefficientShearHorizontalSecond_condition hπ data D hstart hk r j hj) ≫
      coefficientShearAction hπ data K r j hj = o₂ := by
  apply (cancel_mono (E).hom).mp
  rw [coefficientShearAction_pair]
  simp only [Category.assoc, Iso.inv_hom_id, Category.comp_id,
    coefficientShearInitialTensorChart_original]
  exact (finiteHorizontalSecondTensorAction_coefficient hπ data D hstart hk j hj).symm

end FLT.Mazur.WeierstrassDividedDepth
