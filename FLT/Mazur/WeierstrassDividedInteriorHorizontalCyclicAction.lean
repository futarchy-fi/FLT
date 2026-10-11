/-
Copyright (c) 2026 krandder. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: krandder
-/
module

public import FLT.Mazur.WeierstrassDividedInteriorHorizontalCyclicPair
public import FLT.Mazur.WeierstrassDividedInteriorCoefficientAction
public import FLT.Mazur.WeierstrassDividedInteriorTensorOutputGeometry

/-!
# Actual interior actions on the independent universal Laurent pair

The coefficient action and universal projective scaling agree on the original
smooth-times-conic source, with both original component labels preserved.
-/

@[expose] public noncomputable section
open AlgebraicGeometry CategoryTheory Limits IsLocalRing
open MonoidalCategory CartesianMonoidalCategory
open scoped LaurentPolynomial
namespace FLT.Mazur.WeierstrassDividedDepth
open WeierstrassIntegralChart
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
universe u
variable {R : Type u} [CommRing R] [IsDomain R] [IsBezout R] [IsLocalRing R]
  {W : WeierstrassCurve R} {π : R} (hπ : π ≠ 0) {start n depth : ℕ}
  (data : (i : Fin (n + 1)) → Data W π (start + i.val))
  (D : SplitNodeDepth W π depth) (s : ℕ) (hs : s + 1 ≤ n)
  (hstart : 0 < start) (hk : 2 * (start + s + 1) ≤ depth)
  (hp : 2 * (start + s + 1) = depth) (j : Fin s)
local notation "𝕂" => ResidueField R
local notation "e" => data (Fin.mk (j.val + 1) (by omega))
local notation "Z" => positiveEqualityCycleComponent hπ data D s hs hstart hk hp
local notation "τ" => smoothHorizontalTangentUnit D
local notation "z" => smoothHorizontalConicUnit D
local notation "q" => Spec.map (CommRingCat.ofHom
  (AlgHom.toRingHom (ProjectiveLineUniversalAction.laurentPairEvaluation (K := 𝕂) τ⁻¹ z)))
local notation "C" => SmoothHorizontalResidueRing D
local notation "c" => Spec.map (CommRingCat.ofHom (algebraMap 𝕂 C))
local notation "V" => W.map (algebraMap R 𝕂)
local notation "v" => positiveEqualityCyclicSmoothGroupIso D s hk
local notation "o₁" => ProjectiveLineProductOverlap.left 𝕂[T;T⁻¹] ≫
  ProjectiveLineProductCharts.productChartMap 𝕂 𝕂[T;T⁻¹] true
local notation "o₂" => ProjectiveLineProductOverlap.left 𝕂[T;T⁻¹] ≫
  ProjectiveLineProductCharts.productChartMap 𝕂 𝕂[T;T⁻¹] false

local notation "B" => finiteGlobalCoefficientOverAction hπ data (s + 1) hs 𝕂

/-- The actual first interior action is universal scaling on the independent pair. -/
theorem interiorHorizontalFirstCyclicAction_pair :
    q ≫ o₁ ≫ (((v).hom.hom.hom.hom ⊗ₘ Z ⟨j.val + 2, by omega⟩) ≫ B).left =
      q ≫ o₁ ≫
        (ProjectiveLineUniversalAction.act 𝕂 ≫ Z ⟨j.val + 2, by omega⟩).left := by
  have h := congrArg (· ≫ (B).left)
    (interiorHorizontalFirstCyclicInput_pair hπ data D s hs hstart hk hp j)
  have h₂ := congrArg Over.Hom.left
    (interiorHorizontalFirstTensorOutput_over hπ data D s hs hstart hk j)
  have h₃ := interiorHorizontalFirstTensorOutput_universal hπ data D s hs hstart hk hp j
  simpa only [Over.comp_left, Category.assoc, ProjectiveLineUniversalAction.act,
    Over.homMk_left, interiorHorizontalTensorOverPoint] using h.trans (h₂.trans h₃)

/-- The actual second interior action is universal scaling on the independent pair. -/
theorem interiorHorizontalSecondCyclicAction_pair :
    q ≫ o₂ ≫ (((v).hom.hom.hom.hom ⊗ₘ Z ⟨2 * s + 2 - j.val, by omega⟩) ≫ B).left =
      q ≫ o₂ ≫
        (ProjectiveLineUniversalAction.act 𝕂 ≫ Z ⟨2 * s + 2 - j.val, by omega⟩).left := by
  have h := congrArg (· ≫ (B).left)
    (interiorHorizontalSecondCyclicInput_pair hπ data D s hs hstart hk hp j)
  have h₂ := congrArg Over.Hom.left
    (interiorHorizontalSecondTensorOutput_over hπ data D s hs hstart hk j)
  have h₃ := interiorHorizontalSecondTensorOutput_universal hπ data D s hs hstart hk hp j
  simpa only [Over.comp_left, Category.assoc, ProjectiveLineUniversalAction.act,
    Over.homMk_left, interiorHorizontalTensorOverPoint] using h.trans (h₂.trans h₃)

end FLT.Mazur.WeierstrassDividedDepth
