/-
Copyright (c) 2026 krandder. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: krandder
-/
module

public import FLT.Mazur.WeierstrassCoefficientShearSmoothOrbit
public import FLT.Mazur.WeierstrassCoefficientShearRetainedReconstruction

/-!
# Changing the chosen root on the complete coefficient-sheared model

Both presentations reconstruct the same original model. Their full comparison
preserves the original projection, smooth orbit, and independently constructed smooth action.
-/

@[expose] public noncomputable section
open AlgebraicGeometry CategoryTheory Limits
namespace FLT.Mazur.WeierstrassDividedDepth
open WeierstrassIntegralChart
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
universe u
variable {R : Type u} [CommRing R] [IsDomain R] [IsBezout R]
  {W : WeierstrassCurve R} {π : R} (hπ : π ≠ 0) {start n : ℕ}
  (data : (i : Fin (n + 1)) → Data W π (start + i.val))
  (S : Type u) [CommRing S] [Algebra R S] (r s : S) (j : ℕ) (hj : j ≤ n)
local notation "Er" => coefficientShearGluedIso hπ data S r j hj
local notation "Es" => coefficientShearGluedIso hπ data S s j hj
local notation "gr" => coefficientShearGluedStructure hπ data S r j hj
local notation "gs" => coefficientShearGluedStructure hπ data S s j hj
local notation "f" => integralSmoothStructure (W.map (algebraMap R S))

/-- The whole model comparison between two chosen shear parameters. -/
def coefficientShearRootChange : coefficientShearGlued hπ data S r j hj ≅
    coefficientShearGlued hπ data S s j hj := Er ≪≫ (Es).symm
local notation "C" => coefficientShearRootChange hπ data S r s j hj

/-- The full comparison keeps every function of the original model. -/
@[reassoc] theorem coefficientShearRootChange_reconstruction :
    (C).hom ≫ (Es).hom = (Er).hom := by
  simp only [coefficientShearRootChange, Iso.trans_hom, Iso.symm_hom,
    Category.assoc, Iso.inv_hom_id, Category.comp_id]

/-- The comparison retains the actual coefficient morphism. -/
@[reassoc] theorem coefficientShearRootChange_structure : (C).hom ≫ gs = gr := by
  rw [coefficientShearGluedStructure, coefficientShearRootChange_reconstruction_assoc]
  rfl

/-- It retains the complete original integral-model projection. -/
@[reassoc] theorem coefficientShearRootChange_projection :
    (C).hom ≫ coefficientShearGluedProjection hπ data S s j hj =
      coefficientShearGluedProjection hπ data S r j hj := by
  rw [coefficientShearGluedProjection, coefficientShearRootChange_reconstruction_assoc]
  rfl

/-- The independently constructed smooth orbit is unchanged by the chosen shear. -/
@[reassoc] theorem coefficientShearRootChange_smoothEmbedding :
    coefficientShearSmoothEmbedding hπ data S r j hj ≫ (C).hom =
      coefficientShearSmoothEmbedding hπ data S s j hj := by
  apply (cancel_mono (Es).hom).mp
  simp only [Category.assoc, coefficientShearRootChange_reconstruction,
    coefficientShearSmoothEmbedding_reconstruction]

/-- Every original retained tensor chart survives the full change of chosen root. -/
@[reassoc] theorem coefficientShearRootChange_retainedTensorChart (k : ℕ) (hk : k + 1 ≤ j) :
    coefficientShearRetainedTensorChart hπ data S r j hj ⟨k, by omega⟩ ≫ (C).hom =
      coefficientShearRetainedTensorChart hπ data S s j hj ⟨k, by omega⟩ := by
  obtain ⟨m, rfl⟩ := Nat.exists_eq_add_of_le hk
  apply (cancel_mono (coefficientShearGluedIso hπ data S s (k + 1 + m) hj).hom).mp
  simp only [Category.assoc, coefficientShearRootChange_reconstruction,
    coefficientShearRetainedTensorChart_original hπ data S r k (by omega) m hj,
    coefficientShearRetainedTensorChart_original hπ data S s k (by omega) m hj]

variable {T : Scheme.{u}} (p : T ⟶ (integralSmoothOpen (W.map (algebraMap R S))).toScheme)
  (q : T ⟶ coefficientShearGlued hπ data S r j hj)
  (hpq : p ≫ integralSmoothStructure (W.map (algebraMap R S)) =
    q ≫ coefficientShearGluedStructure hπ data S r j hj)

include hpq in
/-- Changing the root keeps the actual smooth input in the action domain. -/
theorem coefficientShearRootChange_pairCondition : p ≫ f = (q ≫ (C).hom) ≫ gs := by
  rw [Category.assoc, coefficientShearRootChange_structure]
  exact hpq

/-- The original smooth action intertwines both complete chosen-root presentations. -/
theorem coefficientShearRootChange_actionPair :
    pullback.lift p q hpq ≫ coefficientShearAction hπ data S r j hj ≫ (C).hom =
      pullback.lift p (q ≫ (C).hom)
          (coefficientShearRootChange_pairCondition hπ data S r s j hj p q hpq) ≫
        coefficientShearAction hπ data S s j hj := by
  rw [← Category.assoc, coefficientShearAction_pair, coefficientShearAction_pair]
  simp only [Category.assoc, coefficientShearRootChange_reconstruction]
  simp only [coefficientShearRootChange, Iso.trans_hom, Iso.symm_hom,
    Iso.inv_hom_id_assoc]

/-- Change the complete model input and retain the original smooth input on the full domain. -/
def coefficientShearRootChangeDomain : coefficientShearActionDomain hπ data S r j hj ⟶
    coefficientShearActionDomain hπ data S s j hj :=
  pullback.lift (pullback.fst f gr) (pullback.snd f gr ≫ (C).hom)
    (coefficientShearRootChange_pairCondition hπ data S r s j hj
      (pullback.fst f gr) (pullback.snd f gr) pullback.condition)

/-- The full domain comparison keeps the independently defined smooth parameter. -/
@[reassoc] theorem coefficientShearRootChange_domain_parameter :
    coefficientShearRootChangeDomain hπ data S r s j hj ≫ pullback.fst f gs =
      pullback.fst f gr := pullback.lift_fst _ _ _

/-- The full domain comparison keeps the whole model reconstruction on its other leg. -/
@[reassoc] theorem coefficientShearRootChange_domain_model :
    coefficientShearRootChangeDomain hπ data S r s j hj ≫ pullback.snd f gs =
      pullback.snd f gr ≫ (C).hom := pullback.lift_snd _ _ _

/-- The entire smooth action intertwines the two complete chosen-root model presentations. -/
@[reassoc] theorem coefficientShearRootChange_action :
    coefficientShearRootChangeDomain hπ data S r s j hj ≫
        coefficientShearAction hπ data S s j hj =
      coefficientShearAction hπ data S r j hj ≫ (C).hom := by
  have H := coefficientShearRootChange_actionPair hπ data S r s j hj
    (pullback.fst f gr) (pullback.snd f gr) pullback.condition
  have hi : pullback.lift (pullback.fst f gr) (pullback.snd f gr) pullback.condition =
      𝟙 (pullback f gr) := by
    apply pullback.hom_ext <;>
      simp only [pullback.lift_fst, pullback.lift_snd, Category.id_comp]
  rw [hi, Category.id_comp] at H
  exact H.symm

end FLT.Mazur.WeierstrassDividedDepth
