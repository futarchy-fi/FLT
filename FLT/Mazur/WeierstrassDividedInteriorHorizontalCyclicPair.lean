/-
Copyright (c) 2026 krandder. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: krandder
-/
module

public import FLT.Mazur.WeierstrassDividedInteriorHorizontalCyclicInput
public import FLT.Mazur.WeierstrassDividedHorizontalCyclicPair

/-!
# The independent cyclic Laurent pair on every interior conic input

Both projections of the universal group-times-component input are the actual
smooth point and the original successive tensor input in the retained model.
This retains the inverse-tangent group coordinate and each original branch label.
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

/-- The first interior universal pair is the original independent successive input. -/
theorem interiorHorizontalFirstCyclicInput_pair :
    q ≫ o₁ ≫ ((v).hom.hom.hom.hom ⊗ₘ Z ⟨j.val + 2, by omega⟩).left =
      (lift (Over.homMk (U := Over.mk c) («V» := (integralSmoothGroup V).X)
        (smoothHorizontalResiduePoint D (by omega))
        (smoothHorizontalResiduePoint_structure D (by omega)))
        (interiorHorizontalTensorOverPoint hπ data D s hs j
          (smoothSuccessiveFirstTensorInput (k := start + j.val) D e
            (by omega) (by omega)))).left := by
  rw [Over.tensorHom_left, Over.lift_left]
  apply pullback.hom_ext
  · simp only [Category.assoc, pullback.lift_fst]
    exact (ProjectiveLineUniversalAction.laurentPairEvaluation_fst_assoc
      τ⁻¹ z true _).trans (smoothHorizontalResiduePoint_cyclic (k := start) D s hk)
  · simp only [Category.assoc, pullback.lift_snd]
    have h := ProjectiveLineUniversalAction.laurentPairEvaluation_snd_assoc
      τ⁻¹ z true (Z ⟨j.val + 2, by omega⟩).left
    rw [smoothHorizontalConicUnit_evaluation] at h
    exact h.trans
      (interiorHorizontalFirstTensorInput_cycle hπ data D s hs hstart hk hp j).symm

/-- The opposite interior universal pair keeps the independent input and its branch label. -/
theorem interiorHorizontalSecondCyclicInput_pair :
    q ≫ o₂ ≫ ((v).hom.hom.hom.hom ⊗ₘ Z ⟨2 * s + 2 - j.val, by omega⟩).left =
      (lift (Over.homMk (U := Over.mk c) («V» := (integralSmoothGroup V).X)
        (smoothHorizontalResiduePoint D (by omega))
        (smoothHorizontalResiduePoint_structure D (by omega)))
        (interiorHorizontalTensorOverPoint hπ data D s hs j
          (smoothSuccessiveSecondTensorInput (k := start + j.val) D e
            (by omega) (by omega)))).left := by
  rw [Over.tensorHom_left, Over.lift_left]
  apply pullback.hom_ext
  · simp only [Category.assoc, pullback.lift_fst]
    exact (ProjectiveLineUniversalAction.laurentPairEvaluation_fst_assoc
      τ⁻¹ z false _).trans (smoothHorizontalResiduePoint_cyclic (k := start) D s hk)
  · simp only [Category.assoc, pullback.lift_snd]
    have h := ProjectiveLineUniversalAction.laurentPairEvaluation_snd_assoc
      τ⁻¹ z false (Z ⟨2 * s + 2 - j.val, by omega⟩).left
    rw [smoothHorizontalConicUnit_evaluation] at h
    exact h.trans
      (interiorHorizontalSecondTensorInput_cycle hπ data D s hs hstart hk hp j).symm

end FLT.Mazur.WeierstrassDividedDepth
