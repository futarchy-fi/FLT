/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.PolygonCompletePointEquationCoefficientProduct
public import FLT.Mazur.PolygonCompletePointStageSectionProducts
public import FLT.Mazur.PolygonCompletePointMarkedNumeratorCoefficient

/-!
# Degree-six compatibility of the retained comparison units

Products of the original normalized complete pole sections compute the
same degree-six frame comparison in two ways. The actual degree-three
unit squared is therefore the actual degree-two unit cubed, over every
full stage ring. Neither original lift is changed.
-/

@[expose] public noncomputable section
open CategoryTheory AlgebraicGeometry Scheme.Modules
namespace FLT.Mazur.PolygonInfinitesimalStages
open FCurve ModuleLineBundleTensorPullback
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
attribute [local irreducible] exactVeroneseProj exactVeroneseProjToBase
  originalStageToCompatibleProj ModuleSheafTensor.tensor divisorLineBundle
variable (K : Type) [Field K] (n : ℕ) (h : 2 ≤ n) [NeZero n]
variable (m : ℕ) (i : Fin n)
local notation "L" => completePointLine K n h i
local notation "S" => completePointPowerStageSection K n h m i
local notation "u" => completePointStageFrameUnit K n h m i

/-- Actual normalized complete sections determine the degree-addition comparison unit. -/
theorem completePointStageFrameUnit_product_of_sections (d k : ℕ)
    (s : Γ(tensorPower (L) d, ⊤)) (v : Γ(tensorPower (L) k, ⊤))
    (hs : completePointStagePoleCoefficient K n h m i d (S d s) = 1)
    (hv : completePointStagePoleCoefficient K n h m i k (S k v) = 1) :
    (u (d + k) : Γ(Spec (.of (Ring K m)), ⊤)) =
      (u d : Γ(Spec (.of (Ring K m)), ⊤)) *
      (u k : Γ(Spec (.of (Ring K m)), ⊤)) := by
  have he := completePointStageEquationCoefficient_product K n h m i d k (S d s) (S k v)
  simpa only [completePointStageEquationCoefficient_compare,
    completePointStagePoleCoefficient_product, hs, hv, mul_one] using he

/-- The original quadratic and cubic comparison units have the same sixth tensor power. -/
theorem completePointStageFrameUnit_three_sq_eq_two_cube :
    (u 3 : Γ(Spec (.of (Ring K m)), ⊤)) ^ 2 =
      (u 2 : Γ(Spec (.of (Ring K m)), ⊤)) ^ 3 := by
  let x := completePointPoleTwoSection K n h i
  let y := completePointProjectiveY K n h i
  have hx : completePointStagePoleCoefficient K n h m i 2 (S 2 x) = 1 :=
    completePointStagePoleTwo_coefficient K n h m i
  have hy : completePointStagePoleCoefficient K n h m i 3 (S 3 y) = 1 :=
    completePointStagePoleThree_coefficient K n h m i
  let xx := SectionGradedMultiplication.mul (L) ⊤ 2 2 x x
  have hxx : completePointStagePoleCoefficient K n h m i 4 (S 4 xx) = 1 := by
    change completePointStagePoleCoefficient K n h m i (2 + 2)
      (S (2 + 2) (SectionGradedMultiplication.mul (L) ⊤ 2 2 x x)) = 1
    rw [completePointPowerStageSection_product, completePointStagePoleCoefficient_product,
      hx, one_mul]
  have h4 := completePointStageFrameUnit_product_of_sections K n h m i 2 2 x x hx hx
  have h6x := completePointStageFrameUnit_product_of_sections K n h m i 4 2 xx x hxx hx
  have h6y := completePointStageFrameUnit_product_of_sections K n h m i 3 3 y y hy hy
  change (u 4 : Γ(Spec (.of (Ring K m)), ⊤)) =
      (u 2 : Γ(Spec (.of (Ring K m)), ⊤)) *
      (u 2 : Γ(Spec (.of (Ring K m)), ⊤)) at h4
  change (u 6 : Γ(Spec (.of (Ring K m)), ⊤)) =
      (u 4 : Γ(Spec (.of (Ring K m)), ⊤)) *
      (u 2 : Γ(Spec (.of (Ring K m)), ⊤)) at h6x
  change (u 6 : Γ(Spec (.of (Ring K m)), ⊤)) =
      (u 3 : Γ(Spec (.of (Ring K m)), ⊤)) *
      (u 3 : Γ(Spec (.of (Ring K m)), ⊤)) at h6y
  rw [pow_two, ← h6y, h6x, h4]
  ring

/-- The unchanged arithmetic marking units satisfy the same degree-six identity. -/
theorem completePointStageArithmeticFrameUnit_three_sq_eq_two_cube :
    (completePointStageArithmeticFrameUnit K n h m i 3 : Ring K m) ^ 2 =
      (completePointStageArithmeticFrameUnit K n h m i 2 : Ring K m) ^ 3 := by
  have he := congrArg (Scheme.ΓSpecIso (.of (Ring K m))).hom.hom
    (completePointStageFrameUnit_three_sq_eq_two_cube K n h m i)
  simp only [map_pow] at he
  exact he

end FLT.Mazur.PolygonInfinitesimalStages
