/-
Copyright (c) 2026 krandder. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: krandder
-/
module

public import FLT.Mazur.WeierstrassDividedInitialTensorGlobalComparison
public import FLT.Mazur.WeierstrassDividedGlobalActionIdentity
public import FLT.Mazur.WeierstrassSmoothHorizontalTensorGlobalAction

/-!
# The concrete horizontal tensor actions in the actual initial finite model

Transport both original residue inputs through the whole-model comparison.
The resulting equalities retain the coefficient projection of the tensor chart.
-/

@[expose] public noncomputable section
open AlgebraicGeometry CategoryTheory Limits IsLocalRing
namespace FLT.Mazur.WeierstrassDividedDepth
open WeierstrassIntegralChart WeierstrassGlobalModification
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
universe u
variable {R : Type u} [CommRing R] [IsDomain R] [IsBezout R] [IsLocalRing R]
  {W : WeierstrassCurve R} {π : R} (hπ : π ≠ 0) {start n depth : ℕ}
  (data : (i : Fin (n + 1)) → Data W π (start + i.val))
  (D : SplitNodeDepth W π depth) (hstart : 0 < start) (hk : 2 * start < depth)
local notation "K" => ResidueField R
local notation "d" => data (Fin.mk 0 (Nat.zero_lt_succ n))
local notation "e" => finiteGlobalInitialIso hπ data
local notation "p" => smoothHorizontalPoint W (π ^ start)
local notation "ψ" => smoothHorizontalInput W (π ^ start)
local notation "j" => originalFractionCoverMap W (π ^ start)
  (Data.b3 d) (Data.b4 d) (Data.b6 d)
  (Data.factor3 d) (Data.factor4 d) (Data.factor6 d) (pow_ne_zero start hπ) (some 1)
local notation "b" => Spec.map (CommRingCat.ofHom ψ) ≫ j
local notation "base" => finiteGlobalStructure hπ data 0 (Nat.zero_le n)
local notation "q" => Spec.map (CommRingCat.ofHom (algebraMap R K))
local notation "g" => globalInitialTensorChart hπ data K 0 (Nat.zero_le n)
local notation "e₁" => smoothHorizontalFirstResidue D start hstart hk hπ
  (Data.b3 d) (Data.b4 d) (Data.b6 d)
  (Data.factor3 d) (Data.factor4 d) (Data.factor6 d)
local notation "e₂" => smoothHorizontalSecondResidue D start hstart hk hπ
  (Data.b3 d) (Data.b4 d) (Data.b6 d)
  (Data.factor3 d) (Data.factor4 d) (Data.factor6 d)

omit hstart hk in
/-- Transport of either original horizontal input preserves its coefficient point. -/
theorem initialHorizontalInput_structure
    (f : SmoothHorizontalProductRing W (π ^ start) →+* SmoothHorizontalResidueRing D) :
    (Spec.map (CommRingCat.ofHom f) ≫ p) ≫ integralSmoothStructure W =
      ((Spec.map (CommRingCat.ofHom f) ≫ b) ≫ (e).inv) ≫ base := by
  have h := smoothHorizontalGlobalInput_structure D d hπ f
  simpa only [Category.assoc, finiteGlobalInitialIso_inv_structure,
    structureMap, Nat.add_zero] using h

/-- The first tensor action is the constructed finite point action at stage zero. -/
theorem initialHorizontalFirstTensorAction_point :
    Spec.map (CommRingCat.ofHom
        (smoothHorizontalFirstTensorAction D d hstart hk hπ).toRingHom) ≫
      g ≫ pullback.snd q base =
        finiteGlobalPointAction hπ data 0 (Nat.zero_le n)
          (Spec.map (CommRingCat.ofHom (e₁).toRingHom) ≫ p)
          ((Spec.map (CommRingCat.ofHom (e₁).toRingHom) ≫ b) ≫ (e).inv)
          (initialHorizontalInput_structure hπ data D (e₁).toRingHom) := by
  apply (cancel_mono (e).hom).mp
  rw [finiteGlobalPointAction_zero_stage, finiteGlobalInitialPointAction_comparison]
  simp only [Category.assoc, Iso.inv_hom_id, Category.comp_id]
  rw [globalInitialTensorChart_initial_comparison]
  exact smoothHorizontalFirstTensorAction_global D d hstart hk hπ

/-- The opposite tensor action retains its original input in the stage-zero action. -/
theorem initialHorizontalSecondTensorAction_point :
    Spec.map (CommRingCat.ofHom
        (smoothHorizontalSecondTensorAction D d hstart hk hπ).toRingHom) ≫
      g ≫ pullback.snd q base =
        finiteGlobalPointAction hπ data 0 (Nat.zero_le n)
          (Spec.map (CommRingCat.ofHom (e₂).toRingHom) ≫ p)
          ((Spec.map (CommRingCat.ofHom (e₂).toRingHom) ≫ b) ≫ (e).inv)
          (initialHorizontalInput_structure hπ data D (e₂).toRingHom) := by
  apply (cancel_mono (e).hom).mp
  rw [finiteGlobalPointAction_zero_stage, finiteGlobalInitialPointAction_comparison]
  simp only [Category.assoc, Iso.inv_hom_id, Category.comp_id]
  rw [globalInitialTensorChart_initial_comparison]
  exact smoothHorizontalSecondTensorAction_global D d hstart hk hπ

end FLT.Mazur.WeierstrassDividedDepth
