/-
Copyright (c) 2026 krandder. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: krandder
-/
module

public import FLT.Mazur.WeierstrassSmoothHorizontalGlobalAction
public import FLT.Mazur.WeierstrassSmoothHorizontalTensorAction
public import FLT.Mazur.WeierstrassHorizontalGlobalChartComparison
public import FLT.Mazur.TensorOpenChart

/-!
# The original tensor equation action contracts to the global single-step action

Both constructed tensor maps retain the horizontal algebra equivalence and
the original equation chart inclusion. Their images in the global model are
therefore the actual action on the independently constructed input points.
-/

@[expose] public noncomputable section
open AlgebraicGeometry CategoryTheory IsLocalRing
open scoped TensorProduct
namespace FLT.Mazur.WeierstrassIntegralChart
open WeierstrassGlobalModification WeierstrassModificationReesCoordinates
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
universe u
variable {R : Type u} [CommRing R] [IsDomain R] [IsBezout R] [IsLocalRing R]
  {W : WeierstrassCurve R} {π : R} {depth k : ℕ} (D : SplitNodeDepth W π depth)
  (d : WeierstrassDividedDepth.Data W π k) (hk0 : 0 < k) (hk : 2 * k < depth) (hπ : π ≠ 0)
local notation "K" => ResidueField R
local notation "C" => SmoothHorizontalResidueRing D
local notation "A" => WeierstrassModificationX.Coordinate W (π ^ k) d.b3 d.b4 d.b6
local notation "E" => WeierstrassModificationX.horizontalReesChartEquiv W (π ^ k)
  d.b3 d.b4 d.b6 d.factor3 d.factor4 d.factor6 (pow_ne_zero k hπ)
local notation "p" => smoothHorizontalPoint W (π ^ k)
local notation "ψ" => smoothHorizontalInput W (π ^ k)
local notation "j" => originalFractionCoverMap W (π ^ k) d.b3 d.b4 d.b6
  d.factor3 d.factor4 d.factor6 (pow_ne_zero k hπ) (some 1)
local notation "b" => Spec.map (CommRingCat.ofHom ψ) ≫ j
local notation "g" => WeierstrassModificationX.xChart W (π ^ k) d.b3 d.b4 d.b6 ≫
  localChart W (π ^ k) d.b3 d.b4 d.b6 d.factor3 d.factor4 d.factor6 (pow_ne_zero k hπ)
local notation "act" => smoothPointAction W (π ^ k) d.b3 d.b4 d.b6
  d.factor3 d.factor4 d.factor6 (pow_ne_zero k hπ)
local notation "e₁" => smoothHorizontalFirstResidue D k hk0 hk hπ
  d.b3 d.b4 d.b6 d.factor3 d.factor4 d.factor6
local notation "e₂" => smoothHorizontalSecondResidue D k hk0 hk hπ
  d.b3 d.b4 d.b6 d.factor3 d.factor4 d.factor6

omit [IsBezout R] in
/-- Restricting the first tensor action to the integral chart gives its original fraction action. -/
theorem smoothHorizontalFirstTensorAction_projection :
    Spec.map (CommRingCat.ofHom
        (smoothHorizontalFirstTensorAction D d hk0 hk hπ).toRingHom) ≫
      TensorOpenChart.projection =
        Spec.map (CommRingCat.ofHom
          ((smoothHorizontalFirstAction D d hk0 hk hπ).comp (E).toAlgHom).toRingHom) := by
  rw [TensorOpenChart.projection, ← Spec.map_comp, ← CommRingCat.ofHom_comp]
  congr 2
  apply RingHom.ext
  intro t
  change smoothHorizontalFirstTensorAction D d hk0 hk hπ ((1 : K) ⊗ₜ[R] t) =
    smoothHorizontalFirstAction D d hk0 hk hπ (E t)
  simp only [smoothHorizontalFirstTensorAction, AlgHom.liftEquiv_tmul,
    one_smul, AlgHom.comp_apply]
  rfl

omit [IsBezout R] in
/-- The opposite tensor action retains the same integral equation chart projection. -/
theorem smoothHorizontalSecondTensorAction_projection :
    Spec.map (CommRingCat.ofHom
        (smoothHorizontalSecondTensorAction D d hk0 hk hπ).toRingHom) ≫
      TensorOpenChart.projection =
        Spec.map (CommRingCat.ofHom
          ((smoothHorizontalSecondAction D d hk0 hk hπ).comp (E).toAlgHom).toRingHom) := by
  rw [TensorOpenChart.projection, ← Spec.map_comp, ← CommRingCat.ofHom_comp]
  congr 2
  apply RingHom.ext
  intro t
  change smoothHorizontalSecondTensorAction D d hk0 hk hπ ((1 : K) ⊗ₜ[R] t) =
    smoothHorizontalSecondAction D d hk0 hk hπ (E t)
  simp only [smoothHorizontalSecondTensorAction, AlgHom.liftEquiv_tmul,
    one_smul, AlgHom.comp_apply]
  rfl

/-- The first tensor equation map lands in the actual global single-step action. -/
theorem smoothHorizontalFirstTensorAction_global :
    Spec.map (CommRingCat.ofHom
        (smoothHorizontalFirstTensorAction D d hk0 hk hπ).toRingHom) ≫
      TensorOpenChart.projection ≫ g =
        act (Spec.map (CommRingCat.ofHom (e₁).toRingHom) ≫ p)
          (Spec.map (CommRingCat.ofHom (e₁).toRingHom) ≫ b)
          (smoothHorizontalGlobalInput_structure D d hπ (e₁).toRingHom) := by
  rw [← Category.assoc, smoothHorizontalFirstTensorAction_projection]
  change Spec.map (CommRingCat.ofHom
    ((smoothHorizontalFirstAction D d hk0 hk hπ).toRingHom.comp
      (E).toAlgHom.toRingHom)) ≫ g = _
  rw [CommRingCat.ofHom_comp, Spec.map_comp, Category.assoc,
    ← originalHorizontalFractionCoverMap_spec]
  exact smoothHorizontalFirstAction_global D d hk0 hk hπ

/-- The opposite tensor equation map gives the same global action on its original input. -/
theorem smoothHorizontalSecondTensorAction_global :
    Spec.map (CommRingCat.ofHom
        (smoothHorizontalSecondTensorAction D d hk0 hk hπ).toRingHom) ≫
      TensorOpenChart.projection ≫ g =
        act (Spec.map (CommRingCat.ofHom (e₂).toRingHom) ≫ p)
          (Spec.map (CommRingCat.ofHom (e₂).toRingHom) ≫ b)
          (smoothHorizontalGlobalInput_structure D d hπ (e₂).toRingHom) := by
  rw [← Category.assoc, smoothHorizontalSecondTensorAction_projection]
  change Spec.map (CommRingCat.ofHom
    ((smoothHorizontalSecondAction D d hk0 hk hπ).toRingHom.comp
      (E).toAlgHom.toRingHom)) ≫ g = _
  rw [CommRingCat.ofHom_comp, Spec.map_comp, Category.assoc,
    ← originalHorizontalFractionCoverMap_spec]
  exact smoothHorizontalSecondAction_global D d hk0 hk hπ

end FLT.Mazur.WeierstrassIntegralChart
