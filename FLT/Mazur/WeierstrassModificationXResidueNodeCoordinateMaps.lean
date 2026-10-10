/-
Copyright (c) 2026 krandder. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: krandder
-/
module

public import FLT.Mazur.WeierstrassModificationXResidueNodeFunctions
public import FLT.Mazur.WeierstrassModificationXResidueNodeGeometry
/-!
# Named node formulas for the original scheme contraction

The coordinate maps computed on both node opens are exactly the existing node
charts followed by the original tensor projection and cubic contraction.
Their normalized projective coordinates retain the ordered node slopes.
-/

@[expose] public noncomputable section

open IsLocalRing AlgebraicGeometry CategoryTheory
namespace FLT.Mazur.WeierstrassModificationX
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
universe u
variable {R : Type u} [CommRing R] [IsDomain R] [IsLocalRing R]
  {W : WeierstrassCurve R} {π : R} {n : ℕ} (D : SplitNodeDepth W π n)
  (k : ℕ) (hk0 : 0 < k) (hk : 2 * k ≤ n) (b3 b4 b6 : R)
  (h3 : W.a₃ = π ^ k * b3) (h4 : W.a₄ = π ^ k * b4)
  (h6 : W.a₆ = (π ^ k) ^ 2 * b6) (hstrict : 2 * k < n)
local notation "K" => ResidueField R
local notation "a" => residue R W.a₁
local notation "N₁" => FirstNodeOpen a
local notation "N₂" => FirstNodeOpen (-a)
local notation "f₁" => residueFirstNodeMap D k hk0 hk b3 b4 b6 h3 h4 h6 hstrict
local notation "f₂" => residueSecondNodeMap D k hk0 hk b3 b4 b6 h3 h4 h6 hstrict
local notation "Q₁" => algebraMap (NodalFiber.Coordinate (0 : K)) N₁ (NodalFiber.q (0 : K))
local notation "Q₂" => algebraMap (NodalFiber.Coordinate (0 : K)) N₂ (NodalFiber.q (0 : K))

/-- The original affine cubic coordinates on the first node open. -/
def residueFirstNodeCoordinateMap : WeierstrassIntegralChart.Coordinate W 2 →ₐ[R] N₁ :=
  (f₁).comp (fromOriginal W (π ^ k) b3 b4 b6 h3 h4 h6)
/-- The original affine cubic coordinates on the second node open. -/
def residueSecondNodeCoordinateMap : WeierstrassIntegralChart.Coordinate W 2 →ₐ[R] N₂ :=
  (f₂).comp (fromOriginal W (π ^ k) b3 b4 b6 h3 h4 h6)

/-- The first node coordinate map is the existing chart followed by tensor projection. -/
@[reassoc] theorem residueFirstNodeChart_projection :
    residueFirstNodeChart D k hk0 hk b3 b4 b6 h3 h4 h6 hstrict ≫
        residueChartProjection k b3 b4 b6 =
    Spec.map (CommRingCat.ofHom (f₁).toRingHom) := by
  change ((Spec.map _ ≫ Spec.map _) ≫ Spec.map _) ≫ Spec.map _ = _
  simp only [← Spec.map_comp]
  rfl
/-- The second node coordinate map is the existing chart followed by tensor projection. -/
@[reassoc] theorem residueSecondNodeChart_projection :
    residueSecondNodeChart D k hk0 hk b3 b4 b6 h3 h4 h6 hstrict ≫
        residueChartProjection k b3 b4 b6 =
    Spec.map (CommRingCat.ofHom (f₂).toRingHom) := by
  change ((Spec.map _ ≫ Spec.map _) ≫ Spec.map _) ≫ Spec.map _ = _
  simp only [← Spec.map_comp]
  rfl

/-- The first coordinate contraction equals the original scheme contraction. -/
@[reassoc] theorem residueFirstNodeChart_coordinateContraction :
    residueFirstNodeChart D k hk0 hk b3 b4 b6 h3 h4 h6 hstrict ≫
        residueChartContraction k b3 b4 b6 h3 h4 h6 =
    Spec.map (CommRingCat.ofHom
      (residueFirstNodeCoordinateMap D k hk0 hk b3 b4 b6 h3 h4 h6 hstrict).toRingHom) ≫
      WeierstrassIntegralChart.integralCurveChart W 2 := by
  rw [residueChartContraction, ← Category.assoc, residueFirstNodeChart_projection]
  change Spec.map _ ≫ (Spec.map _ ≫ _) = _
  rw [← Category.assoc, ← Spec.map_comp]
  rfl
/-- The second coordinate contraction equals the original scheme contraction. -/
@[reassoc] theorem residueSecondNodeChart_coordinateContraction :
    residueSecondNodeChart D k hk0 hk b3 b4 b6 h3 h4 h6 hstrict ≫
        residueChartContraction k b3 b4 b6 h3 h4 h6 =
    Spec.map (CommRingCat.ofHom
      (residueSecondNodeCoordinateMap D k hk0 hk b3 b4 b6 h3 h4 h6 hstrict).toRingHom) ≫
      WeierstrassIntegralChart.integralCurveChart W 2 := by
  rw [residueChartContraction, ← Category.assoc, residueSecondNodeChart_projection]
  change Spec.map _ ≫ (Spec.map _ ≫ _) = _
  rw [← Category.assoc, ← Spec.map_comp]
  rfl

/-- The first node contraction evaluates the original x coordinate. -/
theorem residueFirstNodeCoordinateMap_x :
    residueFirstNodeCoordinateMap D k hk0 hk b3 b4 b6 h3 h4 h6 hstrict
      (WeierstrassIntegralChart.coord W 2 0) = Q₁ * (Q₁ + algebraMap K N₁ a) := by
  rw [residueFirstNodeCoordinateMap, AlgHom.comp_apply, fromOriginal_x,
    residueFirstNodeMap_x]
/-- The first node contraction evaluates the original y coordinate. -/
theorem residueFirstNodeCoordinateMap_y :
    residueFirstNodeCoordinateMap D k hk0 hk b3 b4 b6 h3 h4 h6 hstrict
      (WeierstrassIntegralChart.coord W 2 1) = Q₁ ^ 2 * (Q₁ + algebraMap K N₁ a) := by
  rw [residueFirstNodeCoordinateMap, AlgHom.comp_apply, fromOriginal_y,
    residueFirstNodeMap_y]
/-- The first node contraction evaluates the original z coordinate. -/
theorem residueFirstNodeCoordinateMap_z :
    residueFirstNodeCoordinateMap D k hk0 hk b3 b4 b6 h3 h4 h6 hstrict
      (WeierstrassIntegralChart.coord W 2 2) = 1 := by
  rw [WeierstrassIntegralChart.coord_self, map_one]

/-- The second node contraction evaluates the original x coordinate. -/
theorem residueSecondNodeCoordinateMap_x :
    residueSecondNodeCoordinateMap D k hk0 hk b3 b4 b6 h3 h4 h6 hstrict
      (WeierstrassIntegralChart.coord W 2 0) = Q₂ * (Q₂ - algebraMap K N₂ a) := by
  rw [residueSecondNodeCoordinateMap, AlgHom.comp_apply, fromOriginal_x,
    residueSecondNodeMap_x]
/-- The second node contraction evaluates the original y coordinate. -/
theorem residueSecondNodeCoordinateMap_y :
    residueSecondNodeCoordinateMap D k hk0 hk b3 b4 b6 h3 h4 h6 hstrict
      (WeierstrassIntegralChart.coord W 2 1) = Q₂ * (Q₂ - algebraMap K N₂ a) ^ 2 := by
  rw [residueSecondNodeCoordinateMap, AlgHom.comp_apply, fromOriginal_y,
    residueSecondNodeMap_y]
/-- The second node contraction evaluates the original z coordinate. -/
theorem residueSecondNodeCoordinateMap_z :
    residueSecondNodeCoordinateMap D k hk0 hk b3 b4 b6 h3 h4 h6 hstrict
      (WeierstrassIntegralChart.coord W 2 2) = 1 := by
  rw [WeierstrassIntegralChart.coord_self, map_one]
end FLT.Mazur.WeierstrassModificationX
