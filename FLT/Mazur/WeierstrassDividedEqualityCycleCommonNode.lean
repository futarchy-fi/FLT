/-
Copyright (c) 2026 krandder. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: krandder
-/
module

public import FLT.Mazur.WeierstrassDividedEqualityCycleConstancy
public import FLT.Mazur.WeierstrassDividedExteriorCubicContraction
import all FLT.Mazur.ProjectiveCycleConstantPropagation

/-!
# The common original cubic node for the equality arithmetic cycle

The actual endpoint equations propagate the exterior node value through
all complete exceptional components, as scheme maps to the original cubic.
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
  (D : SplitNodeDepth W π depth) (s : ℕ) (hs : s + 1 ≤ n)
  (hk : 2 * (start + s + 1) ≤ depth) (hp : 2 * (start + s + 1) = depth)
local notation "K" => ResidueField R
local notation "q" => Spec.map (CommRingCat.ofHom (algebraMap R K))
local notation "f" => finiteGlobalStructure hπ data (s + 1) hs
local notation "g" => pullback.snd q f ≫ finiteGlobalContraction hπ data (s + 1) hs
variable (hstart : start = 0)
local notation "Z" => zeroEqualityCycleComponent hπ data D s hs hstart hk hp
local notation "hd" => lt_of_lt_of_le (Nat.mul_pos (by decide) (Nat.succ_pos _)) hk
local notation "v" => PolygonNodePresentation.bOrigin K ≫ OneGonGluing.node K ≫
  Iso.hom (residueOneGonIso D hd) ≫ WeierstrassIntegralChart.integralCoefficientMorphism W

/-- Every original cyclic zero endpoint contracts to the exterior's geometric node. -/
theorem zeroEqualityCycleComponent_zero_cubicContraction (i : Fin (2 * s + 2)) :
    ProjectiveLine.zero K ≫ (Z i).left ≫ g = v := by
  have H := ProjectiveCycleConstantPropagation.zero_eq K (fun j => (Z j).left ≫ g)
    (zeroEqualityCycleComponent_contraction_constant hπ data D s hs hk hp hstart)
    (fun j => ?_) i
  · rw [H, zeroEqualityCycleComponent_exterior]
    exact finalZeroExteriorComponent_zero_cubicContraction hπ data D s hs hstart hk
  · have E := congrArg (fun a => a.left ≫ g)
      (zeroEqualityCycleComponent_endpoints hπ data D s hs hstart hk hp j)
    simpa only [Over.comp_left, ProjectiveLine.zeroSection,
      ProjectiveLine.infinitySection, Over.homMk_left, Category.assoc] using E

/-- Every omitted complete component contracts to that same original node. -/
theorem zeroEqualityCycleComponent_cubicContraction (i : Fin (2 * s + 2)) (hi : i ≠ 0) :
    (Z i).left ≫ g = ProjectiveLine.toBase K ≫ v := by
  rw [zeroEqualityCycleComponent_contraction_constant hπ data D s hs hk hp hstart i hi,
    zeroEqualityCycleComponent_zero_cubicContraction hπ data D s hs hk hp hstart i]

/-- The other endpoint of each omitted component also contracts to the original common node. -/
theorem zeroEqualityCycleComponent_infinity_cubicContraction
    (i : Fin (2 * s + 2)) : ProjectiveLine.infinity K ≫ (Z i).left ≫ g = v := by
  by_cases hi : i = 0
  · subst i
    rw [zeroEqualityCycleComponent_exterior]
    exact finalZeroExteriorComponent_infinity_cubicContraction hπ data D s hs hstart hk
  · rw [zeroEqualityCycleComponent_cubicContraction hπ data D s hs hk hp hstart i hi,
      ProjectiveLine.infinity_toBase_assoc]

end FLT.Mazur.WeierstrassDividedDepth
