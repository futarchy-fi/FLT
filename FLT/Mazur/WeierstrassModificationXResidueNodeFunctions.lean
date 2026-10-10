/-
Copyright (c) 2026 krandder. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: krandder
-/
module

public import FLT.Mazur.WeierstrassModificationXResidueLinesGenerators
public import FLT.Mazur.WeierstrassModificationXFiberSecondNode
/-!
# The original contraction on both named node opens

Compose the original tensor comparison with the existing local node
isomorphisms. Incidence becomes P at each node, while the original slope is Q
at the first and Q-a at the second. The x/y contraction formulas follow from
the original chart functions and preserve this orientation.
-/

@[expose] public noncomputable section

open IsLocalRing
namespace FLT.Mazur.WeierstrassModificationX
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
section
variable {K : Type*} [CommRing K] (a : K)
/-- The actual first node chart on coordinate algebras. -/
def fiberFirstNodeMap : FiberCoordinate a 0 →ₐ[K] FirstNodeOpen a :=
  (firstNodeEquiv a).toAlgHom.comp
    (IsScalarTower.toAlgHom K (FiberCoordinate a 0) (FirstFiberOpen a))
/-- The actual second node chart on coordinate algebras. -/
def fiberSecondNodeMap : FiberCoordinate a 0 →ₐ[K] FirstNodeOpen (-a) :=
  (secondNodeEquiv a).toAlgHom.comp
    (IsScalarTower.toAlgHom K (FiberCoordinate a 0) (SecondFiberOpen a))
/-- The first node chart retains incidence. -/
theorem fiberFirstNodeMap_t : fiberFirstNodeMap a (fiberT a 0) =
    algebraMap _ _ (NodalFiber.p (0 : K)) := firstNodeEquiv_t a
/-- The first node chart retains the original slope. -/
theorem fiberFirstNodeMap_v : fiberFirstNodeMap a (fiberV a 0) =
    algebraMap _ _ (NodalFiber.q (0 : K)) := firstNodeEquiv_v a
/-- The second node chart retains incidence. -/
theorem fiberSecondNodeMap_t : fiberSecondNodeMap a (fiberT a 0) =
    algebraMap _ _ (NodalFiber.p (0 : K)) := secondNodeEquiv_t a
/-- The second node chart retains the original slope. -/
theorem fiberSecondNodeMap_v : fiberSecondNodeMap a (fiberV a 0) =
    algebraMap _ _ (NodalFiber.q (0 : K)) - algebraMap K _ a := by
  have h : fiberSecondNodeMap a (fiberV a 0 + algebraMap K _ a) =
      algebraMap _ _ (NodalFiber.q (0 : K)) := secondNodeEquiv_second a
  rw [map_add, AlgHom.commutes] at h
  exact eq_sub_of_add_eq h
end
variable {R : Type*} [CommRing R] [IsDomain R] [IsLocalRing R]
  {W : WeierstrassCurve R} {π : R} {n : ℕ} (D : SplitNodeDepth W π n)
  (k : ℕ) (hk0 : 0 < k) (hk : 2 * k ≤ n) (b3 b4 b6 : R)
  (h3 : W.a₃ = π ^ k * b3) (h4 : W.a₄ = π ^ k * b4)
  (h6 : W.a₆ = (π ^ k) ^ 2 * b6) (hstrict : 2 * k < n)
local notation "K" => ResidueField R
local notation "a" => residue R W.a₁
local notation "F" => FiberCoordinate a 0
local notation "N₁" => FirstNodeOpen a
local notation "N₂" => FirstNodeOpen (-a)
local notation "f" => residueLinesMap D k hk0 hk b3 b4 b6 h3 h4 h6 hstrict

/-- The original chart map into the first named node open. -/
def residueFirstNodeMap : Coordinate W (π ^ k) b3 b4 b6 →ₐ[R] N₁ :=
  ((fiberFirstNodeMap a).restrictScalars R).comp f

/-- The original chart map into the second named node open. -/
def residueSecondNodeMap : Coordinate W (π ^ k) b3 b4 b6 →ₐ[R] N₂ :=
  ((fiberSecondNodeMap a).restrictScalars R).comp f

local notation "f₁" => residueFirstNodeMap D k hk0 hk b3 b4 b6 h3 h4 h6 hstrict
local notation "f₂" => residueSecondNodeMap D k hk0 hk b3 b4 b6 h3 h4 h6 hstrict
local notation "P₁" => algebraMap (NodalFiber.Coordinate (0 : K)) N₁ (NodalFiber.p (0 : K))
local notation "Q₁" => algebraMap (NodalFiber.Coordinate (0 : K)) N₁ (NodalFiber.q (0 : K))
local notation "P₂" => algebraMap (NodalFiber.Coordinate (0 : K)) N₂ (NodalFiber.p (0 : K))
local notation "Q₂" => algebraMap (NodalFiber.Coordinate (0 : K)) N₂ (NodalFiber.q (0 : K))

/-- The original incidence on the first named node open. -/
theorem residueFirstNodeMap_t : f₁ (t W (π ^ k) b3 b4 b6) = P₁ := by
  change fiberFirstNodeMap a (f _) = _
  rw [residueLinesMap_t, fiberFirstNodeMap_t]
/-- The original slope on the first named node open. -/
theorem residueFirstNodeMap_v : f₁ (v W (π ^ k) b3 b4 b6) = Q₁ := by
  change fiberFirstNodeMap a (f _) = _
  rw [residueLinesMap_v, fiberFirstNodeMap_v]
/-- The original incidence on the second named node open. -/
theorem residueSecondNodeMap_t : f₂ (t W (π ^ k) b3 b4 b6) = P₂ := by
  change fiberSecondNodeMap a (f _) = _
  rw [residueLinesMap_t, fiberSecondNodeMap_t]
/-- The original slope on the second named node open. -/
theorem residueSecondNodeMap_v :
    f₂ (v W (π ^ k) b3 b4 b6) = Q₂ - algebraMap K N₂ a := by
  change fiberSecondNodeMap a (f _) = _
  rw [residueLinesMap_v, fiberSecondNodeMap_v]

/-- The original horizontal contraction on the first named node open. -/
theorem residueFirstNodeMap_x :
    f₁ (x W (π ^ k) b3 b4 b6) = Q₁ * (Q₁ + algebraMap K N₁ a) := by
  change fiberFirstNodeMap a (f _) = _
  rw [residueLinesMap_x, map_mul, map_add, fiberFirstNodeMap_v,
    IsScalarTower.algebraMap_apply R K F, ResidueField.algebraMap_eq, AlgHom.commutes]
/-- The original vertical contraction on the first named node open. -/
theorem residueFirstNodeMap_y :
    f₁ (y W (π ^ k) b3 b4 b6) = Q₁ ^ 2 * (Q₁ + algebraMap K N₁ a) := by
  rw [y, map_mul, residueFirstNodeMap_x, residueFirstNodeMap_v]
  ring

/-- The original horizontal contraction on the second named node open. -/
theorem residueSecondNodeMap_x :
    f₂ (x W (π ^ k) b3 b4 b6) = Q₂ * (Q₂ - algebraMap K N₂ a) := by
  change fiberSecondNodeMap a (f _) = _
  rw [residueLinesMap_x, map_mul, map_add, fiberSecondNodeMap_v,
    IsScalarTower.algebraMap_apply R K F, ResidueField.algebraMap_eq, AlgHom.commutes]
  ring
/-- The original vertical contraction on the second named node open. -/
theorem residueSecondNodeMap_y :
    f₂ (y W (π ^ k) b3 b4 b6) = Q₂ * (Q₂ - algebraMap K N₂ a) ^ 2 := by
  rw [y, map_mul, residueSecondNodeMap_x, residueSecondNodeMap_v]
  ring
end FLT.Mazur.WeierstrassModificationX
