/-
Copyright (c) 2026 krandder. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: krandder
-/
module

public import FLT.Mazur.WeierstrassModificationXFullNodeFunctions
public import FLT.Mazur.WeierstrassModificationXResidueFullNodeGeometry
public import FLT.Mazur.WeierstrassModificationXResidueNamedGenerators

/-!
# The original contraction functions on both full residue node charts

The actual residue normal map retains the middle-depth constant. Composing
with the proved ambient charts gives the original t, v, x and y functions;
x is the conic factor q times a unit, and y is x times the original slope.
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
local notation "K" => ResidueField R
local notation "a" => residue R W.a₁
local notation "c" => residue R b6
local notation "ha" => residue_tangent_isUnit D
local notation "F" => FiberCoordinate a c
local notation "L₀" => FullNodeOpen a c
local notation "L₁" => FullNodeOpen (-a) c
local notation "f" => residueNormalMap D k hk0 hk b3 b4 b6 h3 h4

/-- The original modification functions on the first full ambient node. -/
def residueFullFirstNodeMap : Coordinate W (π ^ k) b3 b4 b6 →ₐ[R] L₀ :=
  ((fiberFullFirstNodeMap a c ha).restrictScalars R).comp f
/-- The original modification functions on the second full ambient node. -/
def residueFullSecondNodeMap : Coordinate W (π ^ k) b3 b4 b6 →ₐ[R] L₁ :=
  ((fiberFullSecondNodeMap a c ha).restrictScalars R).comp f
local notation "g₀" => residueFullFirstNodeMap D k hk0 hk b3 b4 b6 h3 h4
local notation "g₁" => residueFullSecondNodeMap D k hk0 hk b3 b4 b6 h3 h4

/-- The original incidence function on the first full residue node. -/
theorem residueFullFirstNodeMap_t : g₀ (t W (π ^ k) b3 b4 b6) = fullNodeInverseT a c := by
  change fiberFullFirstNodeMap a c ha (f _) = _
  rw [residueNormalMap_t, fiberFullFirstNodeMap_t]
/-- The original slope function on the first full residue node. -/
theorem residueFullFirstNodeMap_v : g₀ (v W (π ^ k) b3 b4 b6) = fullNodeInverseV a c := by
  change fiberFullFirstNodeMap a c ha (f _) = _
  rw [residueNormalMap_v, fiberFullFirstNodeMap_v]
/-- The original incidence function on the second full residue node. -/
theorem residueFullSecondNodeMap_t : g₁ (t W (π ^ k) b3 b4 b6) = fullNodeInverseT (-a) c := by
  change fiberFullSecondNodeMap a c ha (f _) = _
  rw [residueNormalMap_t, fiberFullSecondNodeMap_t]
/-- The original slope function keeps the second tangent translation. -/
theorem residueFullSecondNodeMap_v : g₁ (v W (π ^ k) b3 b4 b6) =
    fullNodeInverseV (-a) c - algebraMap K L₁ a := by
  change fiberFullSecondNodeMap a c ha (f _) = _
  rw [residueNormalMap_v, fiberFullSecondNodeMap_v]

/-- The original x function is the conic branch coordinate times the first tangent unit. -/
theorem residueFullFirstNodeMap_x : g₀ (x W (π ^ k) b3 b4 b6) =
    fullNodeQ a c * (fullNodeInverseV a c + algebraMap K L₀ a) := by
  change fiberFullFirstNodeMap a c ha (f _) = _
  rw [residueNormalMap_x, residueNormalMap_v, residueNormalMap_t,
    IsScalarTower.algebraMap_apply R K F, IsScalarTower.algebraMap_apply R K F]
  exact fiberFullFirstNodeMap_conic a c ha

/-- The original x function retains the opposite orientation on the second chart. -/
theorem residueFullSecondNodeMap_x : g₁ (x W (π ^ k) b3 b4 b6) =
    fullNodeQ (-a) c * (fullNodeInverseV (-a) c + algebraMap K L₁ (-a)) := by
  change fiberFullSecondNodeMap a c ha (f _) = _
  rw [residueNormalMap_x, residueNormalMap_v, residueNormalMap_t,
    IsScalarTower.algebraMap_apply R K F, IsScalarTower.algebraMap_apply R K F]
  exact fiberFullSecondNodeMap_conic a c ha

/-- The original y function on the first chart is x times the original slope. -/
theorem residueFullFirstNodeMap_y : g₀ (y W (π ^ k) b3 b4 b6) =
    (fullNodeQ a c * (fullNodeInverseV a c + algebraMap K L₀ a)) *
      fullNodeInverseV a c := by
  change fiberFullFirstNodeMap a c ha (f _) = _
  rw [residueNormalMap_y, map_mul]
  change g₀ (x W (π ^ k) b3 b4 b6) * g₀ (v W (π ^ k) b3 b4 b6) = _
  rw [residueFullFirstNodeMap_x, residueFullFirstNodeMap_v]

/-- The original y function on the second chart keeps the untranslated original slope. -/
theorem residueFullSecondNodeMap_y : g₁ (y W (π ^ k) b3 b4 b6) =
    (fullNodeQ (-a) c * (fullNodeInverseV (-a) c + algebraMap K L₁ (-a))) *
      (fullNodeInverseV (-a) c - algebraMap K L₁ a) := by
  change fiberFullSecondNodeMap a c ha (f _) = _
  rw [residueNormalMap_y, map_mul]
  change g₁ (x W (π ^ k) b3 b4 b6) * g₁ (v W (π ^ k) b3 b4 b6) = _
  rw [residueFullSecondNodeMap_x, residueFullSecondNodeMap_v]

/-- The first computed function map is exactly the original tensor-fiber projection. -/
@[reassoc] theorem residueFullFirstNodeChart_projection :
    residueFullFirstNodeChart D k hk0 hk b3 b4 b6 h3 h4 ≫
        residueChartProjection k b3 b4 b6 =
      Spec.map (CommRingCat.ofHom (g₀).toRingHom) := by
  rw [residueFullFirstNodeChart, Category.assoc, residueFiberIso_projection,
    fullFirstNodeChart_eq_spec, ← Spec.map_comp]
  rfl

/-- The second computed function map is exactly the same original projection. -/
@[reassoc] theorem residueFullSecondNodeChart_projection :
    residueFullSecondNodeChart D k hk0 hk b3 b4 b6 h3 h4 ≫
        residueChartProjection k b3 b4 b6 =
      Spec.map (CommRingCat.ofHom (g₁).toRingHom) := by
  rw [residueFullSecondNodeChart, Category.assoc, residueFiberIso_projection,
    fullSecondNodeChart_eq_spec, ← Spec.map_comp]
  rfl

end FLT.Mazur.WeierstrassModificationX
