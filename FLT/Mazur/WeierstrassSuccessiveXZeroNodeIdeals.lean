/-
Copyright (c) 2026 krandder. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: krandder
-/
module

public import FLT.Mazur.WeierstrassSuccessiveXZeroNodeMaps

/-!
# The original component ideals on the first successive residue nodes

The original incidence and horizontal ideals become exactly the two node
branches. Their scheme-theoretic intersection is the full node origin.
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

local notation "t₀" => tensorCoord W (π ^ k) π b3 b4 b6 K 0
local notation "u₀" => tensorCoord W (π ^ k) π b3 b4 b6 K 2

/-- The first node retains the entire original incidence component ideal. -/
theorem zeroFirstNodeMap_incidenceIdeal :
    Ideal.map (zeroFirstNodeMap D k hk0 hk b3 b4 b6 h3 h4).toRingHom
      (Ideal.span {t₀}) = Ideal.span {fullNodeP a c} := by
  rw [Ideal.map_span, Set.image_singleton]
  change Ideal.span {zeroFirstNodeMap D k hk0 hk b3 b4 b6 h3 h4 t₀} = _
  rw [zeroFirstNodeMap_t, fullNodeInverseT,
    Ideal.span_singleton_mul_right_unit (fullNodeInv_isUnit a c),
    Ideal.span_singleton_mul_left_unit ((ha).map (algebraMap K L₀))]

/-- The first node retains the entire original conic component ideal. -/
theorem zeroFirstNodeMap_conicIdeal :
    Ideal.map (zeroFirstNodeMap D k hk0 hk b3 b4 b6 h3 h4).toRingHom
      (Ideal.span {u₀}) = Ideal.span {fullNodeQ a c} := by
  rw [Ideal.map_span, Set.image_singleton]
  change Ideal.span {zeroFirstNodeMap D k hk0 hk b3 b4 b6 h3 h4 u₀} = _
  rw [zeroFirstNodeMap_u,
    Ideal.span_singleton_mul_right_unit (fullNodeInverseV_add_isUnit a c)]

/-- The first actual component intersection is exactly the full node origin ideal. -/
theorem zeroFirstNodeMap_intersectionIdeal :
    Ideal.map (zeroFirstNodeMap D k hk0 hk b3 b4 b6 h3 h4).toRingHom
      (Ideal.span {t₀} ⊔ Ideal.span {u₀}) = fullNodeOriginIdeal a c := by
  rw [Ideal.map_sup, zeroFirstNodeMap_incidenceIdeal, zeroFirstNodeMap_conicIdeal]
  rfl

/-- The second node retains the entire original incidence component ideal. -/
theorem zeroSecondNodeMap_incidenceIdeal :
    Ideal.map (zeroSecondNodeMap D k hk0 hk b3 b4 b6 h3 h4).toRingHom
      (Ideal.span {t₀}) = Ideal.span {fullNodeP (-a) c} := by
  rw [Ideal.map_span, Set.image_singleton]
  change Ideal.span {zeroSecondNodeMap D k hk0 hk b3 b4 b6 h3 h4 t₀} = _
  rw [zeroSecondNodeMap_t, fullNodeInverseT,
    Ideal.span_singleton_mul_right_unit (fullNodeInv_isUnit (-a) c),
    Ideal.span_singleton_mul_left_unit (((ha).neg).map (algebraMap K L₁))]

/-- The second node retains the entire original conic component ideal. -/
theorem zeroSecondNodeMap_conicIdeal :
    Ideal.map (zeroSecondNodeMap D k hk0 hk b3 b4 b6 h3 h4).toRingHom
      (Ideal.span {u₀}) = Ideal.span {fullNodeQ (-a) c} := by
  rw [Ideal.map_span, Set.image_singleton]
  change Ideal.span {zeroSecondNodeMap D k hk0 hk b3 b4 b6 h3 h4 u₀} = _
  rw [zeroSecondNodeMap_u,
    Ideal.span_singleton_mul_right_unit (fullNodeInverseV_add_isUnit (-a) c)]

/-- The second actual component intersection is exactly the full node origin ideal. -/
theorem zeroSecondNodeMap_intersectionIdeal :
    Ideal.map (zeroSecondNodeMap D k hk0 hk b3 b4 b6 h3 h4).toRingHom
      (Ideal.span {t₀} ⊔ Ideal.span {u₀}) = fullNodeOriginIdeal (-a) c := by
  rw [Ideal.map_sup, zeroSecondNodeMap_incidenceIdeal, zeroSecondNodeMap_conicIdeal]
  rfl

end FLT.Mazur.WeierstrassSuccessiveX
