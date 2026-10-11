/-
Copyright (c) 2026 krandder. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: krandder
-/
module

public import FLT.Mazur.WeierstrassDividedHorizontalCoefficientPointAction
public import FLT.Mazur.WeierstrassDividedInitialTensorActionGeometry

/-!
# Original horizontal inputs on the labeled cyclic components

The coefficient action now uses the actual punctures of component one and
of the final component, with the original independent smooth parameter.
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


/-- The original first tensor input is the puncture of cyclic component one. -/
theorem initialHorizontalFirstTensorInput_cycle :
    Spec.map (CommRingCat.ofHom
        (smoothHorizontalFirstTensorInput (k := start) D d hstart (by omega)).toRingHom) ≫ g =
      b ≫ ProjectiveLine.overlapLeft 𝕂 ≫ ProjectiveLine.right 𝕂 ≫ (Z 1).left := by
  rw [smoothHorizontalFirstTensorInput, lineSpec_comp, lineSpec_comp, lineSpec_comp]
  simp only [Category.assoc]
  exact congrArg (b ≫ ·) (initialConicFirstPuncture_cycle hπ data D s hs hstart hk hp)

/-- The original opposite tensor input is the puncture of the final cyclic component. -/
theorem initialHorizontalSecondTensorInput_cycle :
    Spec.map (CommRingCat.ofHom
        (smoothHorizontalSecondTensorInput (k := start) D d hstart (by omega)).toRingHom) ≫ g =
      b ≫ ProjectiveLine.overlapLeft 𝕂 ≫ ProjectiveLine.left 𝕂 ≫
        (Z ⟨2 * s + 3, by omega⟩).left := by
  rw [smoothHorizontalSecondTensorInput, lineSpec_comp, lineSpec_comp, lineSpec_comp]
  simp only [Category.assoc]
  exact congrArg (b ≫ ·) (initialConicSecondPuncture_cycle hπ data D s hs hstart hk hp)

/-- The actual relative action agrees with universal scaling on the first original input. -/
theorem initialHorizontalFirstCoefficientAction_universal :
    (lift (Over.homMk (U := Over.mk c)
  («V» := (integralSmoothGroup V).X)
  (smoothHorizontalResiduePoint D (by omega))
  (smoothHorizontalResiduePoint_structure D (by omega)))
      (horizontalTensorOverPoint hπ data D (s + 1) hs
        (smoothHorizontalFirstTensorInput (k := start) D d hstart (by omega))) ≫ B).left =
      q ≫ ProjectiveLineProductOverlap.left 𝕂[T;T⁻¹] ≫
        ProjectiveLineProductCharts.productChartMap 𝕂 𝕂[T;T⁻¹] true ≫
          ProjectiveLineUniversalAction.action 𝕂 ≫ (Z 1).left := by
  rw [finiteHorizontalFirstTensorAction_over]
  exact initialHorizontalFirstTensorAction_universal hπ data D s hs hstart hk hp

/-- Universal scaling also describes the actual relative action on the opposite input. -/
theorem initialHorizontalSecondCoefficientAction_universal :
    (lift (Over.homMk (U := Over.mk c)
  («V» := (integralSmoothGroup V).X)
  (smoothHorizontalResiduePoint D (by omega))
  (smoothHorizontalResiduePoint_structure D (by omega)))
      (horizontalTensorOverPoint hπ data D (s + 1) hs
        (smoothHorizontalSecondTensorInput (k := start) D d hstart (by omega))) ≫ B).left =
      q ≫ ProjectiveLineProductOverlap.left 𝕂[T;T⁻¹] ≫
        ProjectiveLineProductCharts.productChartMap 𝕂 𝕂[T;T⁻¹] false ≫
          ProjectiveLineUniversalAction.action 𝕂 ≫ (Z ⟨2 * s + 3, by omega⟩).left := by
  rw [finiteHorizontalSecondTensorAction_over]
  exact initialHorizontalSecondTensorAction_universal hπ data D s hs hstart hk hp

end FLT.Mazur.WeierstrassDividedDepth
