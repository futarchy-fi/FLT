/-
Copyright (c) 2026 krandder. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: krandder
-/
module

public import FLT.Mazur.WeierstrassDividedHorizontalCyclicInput
public import FLT.Mazur.ProjectiveLineUniversalLaurentProjections

/-!
# The actual action on the independent cyclic Laurent pair

Both relative action morphisms agree on the original smooth-times-conic source,
now expressed as restrictions of the same universal product morphism.
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
local notation "d" => data (Fin.mk 0 (Nat.zero_lt_succ n))
local notation "g" => globalInitialTensorChart hπ data 𝕂 (s + 1) hs
local notation "Z" => positiveEqualityCycleComponent hπ data D s hs hstart hk hp
local notation "b" => Spec.map
  (CommRingCat.ofHom (AlgHom.toRingHom (smoothHorizontalResidueConic D)))
local notation "τ" => smoothHorizontalTangentUnit D
local notation "z" => smoothHorizontalConicUnit D
local notation "q" => Spec.map (CommRingCat.ofHom
  (AlgHom.toRingHom (ProjectiveLineUniversalAction.laurentPairEvaluation (K := 𝕂) τ⁻¹ z)))
local notation "B" => finiteGlobalCoefficientOverAction hπ data (s + 1) hs 𝕂
local notation "C" => SmoothHorizontalResidueRing D
local notation "c" => Spec.map (CommRingCat.ofHom (algebraMap 𝕂 C))
local notation "V" => W.map (algebraMap R 𝕂)


local notation "v" => positiveEqualityCyclicSmoothGroupIso D s hk
local notation "o₁" => ProjectiveLineProductOverlap.left 𝕂[T;T⁻¹] ≫
  ProjectiveLineProductCharts.productChartMap 𝕂 𝕂[T;T⁻¹] true
local notation "o₂" => ProjectiveLineProductOverlap.left 𝕂[T;T⁻¹] ≫
  ProjectiveLineProductCharts.productChartMap 𝕂 𝕂[T;T⁻¹] false

omit hπ data s hs hstart hk hp [IsDomain R] [IsBezout R] in
/-- Evaluation at the conic unit is the entire original conic projection. -/
theorem smoothHorizontalConicUnit_evaluation :
    LaurentUnitPoints.evalUnit z = smoothHorizontalResidueConic D := by
  have h : LaurentUnitPoints.pointUnit (smoothHorizontalResidueConic D) = z := by
    apply Units.ext
    exact (smoothHorizontalConicUnit_val D).symm
  rw [← h, LaurentUnitPoints.evalUnit_pointUnit]

/-- The universal input pair is exactly the original first relative action input. -/
theorem initialHorizontalFirstCyclicInput_pair :
    q ≫ o₁ ≫ ((v).hom.hom.hom.hom ⊗ₘ Z 1).left =
      (lift (Over.homMk (U := Over.mk c) («V» := (integralSmoothGroup V).X)
        (smoothHorizontalResiduePoint D (by omega))
        (smoothHorizontalResiduePoint_structure D (by omega)))
        (horizontalTensorOverPoint hπ data D (s + 1) hs
          (smoothHorizontalFirstTensorInput (k := start) D d hstart (by omega)))).left := by
  rw [Over.tensorHom_left, Over.lift_left]
  apply pullback.hom_ext
  · simp only [Category.assoc, pullback.lift_fst]
    exact (ProjectiveLineUniversalAction.laurentPairEvaluation_fst_assoc
      τ⁻¹ z true _).trans (smoothHorizontalResiduePoint_cyclic (k := start) D s hk)
  · simp only [Category.assoc, pullback.lift_snd]
    have h := ProjectiveLineUniversalAction.laurentPairEvaluation_snd_assoc
      τ⁻¹ z true (Z 1).left
    rw [smoothHorizontalConicUnit_evaluation] at h
    exact h.trans (initialHorizontalFirstTensorInput_cycle hπ data D s hs hstart hk hp).symm

/-- Actual component-one action and universal scaling agree on the independent pair. -/
theorem initialHorizontalFirstCyclicAction_pair :
    q ≫ o₁ ≫ (((v).hom.hom.hom.hom ⊗ₘ Z 1) ≫ B).left =
      q ≫ o₁ ≫ (ProjectiveLineUniversalAction.act 𝕂 ≫ Z 1).left := by
  have h := congrArg (· ≫ (B).left)
    (initialHorizontalFirstCyclicInput_pair hπ data D s hs hstart hk hp)
  have h₂ := initialHorizontalFirstCoefficientAction_universal hπ data D s hs hstart hk hp
  simpa only [Over.comp_left, Category.assoc, ProjectiveLineUniversalAction.act,
    Over.homMk_left] using h.trans h₂

/-- The universal input pair is exactly the original opposite relative action input. -/
theorem initialHorizontalSecondCyclicInput_pair :
    q ≫ o₂ ≫ ((v).hom.hom.hom.hom ⊗ₘ Z ⟨2 * s + 3, by omega⟩).left =
      (lift (Over.homMk (U := Over.mk c) («V» := (integralSmoothGroup V).X)
        (smoothHorizontalResiduePoint D (by omega))
        (smoothHorizontalResiduePoint_structure D (by omega)))
        (horizontalTensorOverPoint hπ data D (s + 1) hs
          (smoothHorizontalSecondTensorInput (k := start) D d hstart (by omega)))).left := by
  rw [Over.tensorHom_left, Over.lift_left]
  apply pullback.hom_ext
  · simp only [Category.assoc, pullback.lift_fst]
    exact (ProjectiveLineUniversalAction.laurentPairEvaluation_fst_assoc
      τ⁻¹ z false _).trans (smoothHorizontalResiduePoint_cyclic (k := start) D s hk)
  · simp only [Category.assoc, pullback.lift_snd]
    have h := ProjectiveLineUniversalAction.laurentPairEvaluation_snd_assoc
      τ⁻¹ z false (Z ⟨2 * s + 3, by omega⟩).left
    rw [smoothHorizontalConicUnit_evaluation] at h
    exact h.trans (initialHorizontalSecondTensorInput_cycle hπ data D s hs hstart hk hp).symm

/-- Actual final-component action and universal scaling agree on the independent pair. -/
theorem initialHorizontalSecondCyclicAction_pair :
    q ≫ o₂ ≫ (((v).hom.hom.hom.hom ⊗ₘ Z ⟨2 * s + 3, by omega⟩) ≫ B).left =
      q ≫ o₂ ≫ (ProjectiveLineUniversalAction.act 𝕂 ≫ Z ⟨2 * s + 3, by omega⟩).left := by
  have h := congrArg (· ≫ (B).left)
    (initialHorizontalSecondCyclicInput_pair hπ data D s hs hstart hk hp)
  have h₂ := initialHorizontalSecondCoefficientAction_universal hπ data D s hs hstart hk hp
  simpa only [Over.comp_left, Category.assoc, ProjectiveLineUniversalAction.act,
    Over.homMk_left] using h.trans h₂

end FLT.Mazur.WeierstrassDividedDepth
