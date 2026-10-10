/-
Copyright (c) 2026 krandder. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: krandder
-/
module

public import FLT.Mazur.WeierstrassSuccessiveXZeroResidue
public import FLT.Mazur.WeierstrassSuccessiveXTensorContraction
public import FLT.Mazur.WeierstrassModificationXFullNodeFunctions

/-!
# Ordered full node functions on the first successive tensor fiber

All three original generators are retained on both ambient node charts.
The horizontal generator becomes the conic branch times its tangent unit.
-/

@[expose] public noncomputable section
open IsLocalRing AlgebraicGeometry CategoryTheory
namespace FLT.Mazur.WeierstrassSuccessiveX
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
variable {R : Type*} [CommRing R] [IsDomain R] [IsLocalRing R]
  {W : WeierstrassCurve R} {π : R} {depth : ℕ} (D : SplitNodeDepth W π depth)
  (k : ℕ) (hk0 : k = 0) (hk : 2 * (k + 1) ≤ depth) (b3 b4 b6 : R)
  (h3 : W.a₃ = π ^ (k + 1) * b3) (h4 : W.a₄ = π ^ (k + 1) * b4)
local notation "K" => ResidueField R
local notation "a" => residue R W.a₁
local notation "c" => residue R b6
local notation "F" => WeierstrassModificationX.FiberCoordinate a c
local notation "T" => ScalarExtension W (π ^ k) π b3 b4 b6 K
local notation "ha" => D.a₁_unit.map (residue R)
open WeierstrassModificationX
local notation "L₀" => FullNodeOpen a c
local notation "L₁" => FullNodeOpen (-a) c
local notation "E" => zeroResidueFiberEquiv D k hk0 hk b3 b4 b6 h3 h4

/-- Original tensor functions on the first ordered full node. -/
def zeroFirstNodeMap : T →ₐ[K] L₀ := (fiberFullFirstNodeMap a c ha).comp (E).toAlgHom

/-- Original tensor functions on the opposite ordered full node. -/
def zeroSecondNodeMap : T →ₐ[K] L₁ := (fiberFullSecondNodeMap a c ha).comp (E).toAlgHom

/-- The first full node retains the original t coordinate and its orientation. -/
theorem zeroFirstNodeMap_t :
    zeroFirstNodeMap D k hk0 hk b3 b4 b6 h3 h4
      (tensorCoord W (π ^ k) π b3 b4 b6 K 0) =
        fullNodeInverseT a c := by
  change fiberFullFirstNodeMap a c ha (E _) = _
  rw [zeroResidueFiberEquiv_t]
  exact fiberFullFirstNodeMap_t a c ha

/-- The first full node retains the original v coordinate and its orientation. -/
theorem zeroFirstNodeMap_v :
    zeroFirstNodeMap D k hk0 hk b3 b4 b6 h3 h4
      (tensorCoord W (π ^ k) π b3 b4 b6 K 1) =
        fullNodeInverseV a c := by
  change fiberFullFirstNodeMap a c ha (E _) = _
  rw [zeroResidueFiberEquiv_v]
  exact fiberFullFirstNodeMap_v a c ha

/-- The first full node retains the original u coordinate and its orientation. -/
theorem zeroFirstNodeMap_u :
    zeroFirstNodeMap D k hk0 hk b3 b4 b6 h3 h4
      (tensorCoord W (π ^ k) π b3 b4 b6 K 2) =
        fullNodeQ a c * (fullNodeInverseV a c + algebraMap K L₀ a) := by
  change fiberFullFirstNodeMap a c ha (E _) = _
  rw [zeroResidueFiberEquiv_u]
  exact fiberFullFirstNodeMap_conic a c ha

/-- The second full node retains the original t coordinate and its orientation. -/
theorem zeroSecondNodeMap_t :
    zeroSecondNodeMap D k hk0 hk b3 b4 b6 h3 h4
      (tensorCoord W (π ^ k) π b3 b4 b6 K 0) =
        fullNodeInverseT (-a) c := by
  change fiberFullSecondNodeMap a c ha (E _) = _
  rw [zeroResidueFiberEquiv_t]
  exact fiberFullSecondNodeMap_t a c ha

/-- The second full node retains the original v coordinate and its orientation. -/
theorem zeroSecondNodeMap_v :
    zeroSecondNodeMap D k hk0 hk b3 b4 b6 h3 h4
      (tensorCoord W (π ^ k) π b3 b4 b6 K 1) =
        fullNodeInverseV (-a) c - algebraMap K L₁ a := by
  change fiberFullSecondNodeMap a c ha (E _) = _
  rw [zeroResidueFiberEquiv_v]
  exact fiberFullSecondNodeMap_v a c ha

/-- The second full node retains the original u coordinate and its orientation. -/
theorem zeroSecondNodeMap_u :
    zeroSecondNodeMap D k hk0 hk b3 b4 b6 h3 h4
      (tensorCoord W (π ^ k) π b3 b4 b6 K 2) =
        fullNodeQ (-a) c * (fullNodeInverseV (-a) c + algebraMap K L₁ (-a)) := by
  change fiberFullSecondNodeMap a c ha (E _) = _
  rw [zeroResidueFiberEquiv_u]
  exact fiberFullSecondNodeMap_conic a c ha

end FLT.Mazur.WeierstrassSuccessiveX
