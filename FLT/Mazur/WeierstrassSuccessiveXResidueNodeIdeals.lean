/-
Copyright (c) 2026 krandder. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: krandder
-/
module

public import FLT.Mazur.WeierstrassSuccessiveXResidueNodeMaps

/-!
# Ordered component ideals in the actual tensor node charts

The conic ideal becomes the u-zero branch in both charts. The original
zero-slope and opposite-slope lines become the z-zero branch in order.
-/

@[expose] public noncomputable section
open IsLocalRing
namespace FLT.Mazur.WeierstrassSuccessiveX
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
variable {R : Type*} [CommRing R] [IsDomain R] [IsLocalRing R]
  {W : WeierstrassCurve R} {π : R} {n : ℕ} (D : SplitNodeDepth W π n)
  (k : ℕ) (hk0 : 0 < k) (hk : 2 * (k + 1) ≤ n) (b3 b4 b6 : R)
  (h3 : W.a₃ = π ^ (k + 1) * b3) (h4 : W.a₄ = π ^ (k + 1) * b4)
local notation "K" => ResidueField R
local notation "W₀" => W.map (residue R)
local notation "c" => residue R b6
local notation "T" => ScalarExtension W (π ^ k) π b3 b4 b6 K
local notation "N" => MiddleNodeOpen c
local notation "F" => residueFirstNodeMap D k hk0 hk b3 b4 b6 h3 h4
local notation "G" => residueSecondNodeMap D k hk0 hk b3 b4 b6 h3 h4
local notation "t" => tensorCoord W (π ^ k) π b3 b4 b6 K 0
local notation "v" => tensorCoord W (π ^ k) π b3 b4 b6 K 1
local notation "u" => tensorCoord W (π ^ k) π b3 b4 b6 K 2

/-- The original conic component is exactly the first node's u-zero branch. -/
theorem residueFirstNodeMap_conicIdeal :
    Ideal.map (AlgHom.toRingHom F) (Ideal.span {u}) = Ideal.span {middleNodeU c} := by
  rw [Ideal.map_span, Set.image_singleton]
  change Ideal.span {F u} = _
  rw [residueFirstNodeMap_coord]
  rfl

/-- The same original conic is the second node's u-zero branch. -/
theorem residueSecondNodeMap_conicIdeal :
    Ideal.map (AlgHom.toRingHom G) (Ideal.span {u}) = Ideal.span {middleNodeU c} := by
  rw [Ideal.map_span, Set.image_singleton]
  change Ideal.span {G u} = _
  rw [residueSecondNodeMap_coord]
  rfl

/-- The original zero-slope line maps to the first ordered node's z-zero branch. -/
theorem residueFirstNodeMap_lineIdeal :
    Ideal.map (AlgHom.toRingHom F) (Ideal.span {t, v}) =
        Ideal.span {middleNodeZ c} := by
  rw [Ideal.map_span, Set.image_pair]
  change Ideal.span {F t, F v} = _
  rw [residueFirstNodeMap_coord, residueFirstNodeMap_coord]
  change Ideal.span {middleNodeT (WeierstrassCurve.a₁ W₀) c,
    middleNodeV (WeierstrassCurve.a₁ W₀) c} = _
  rw [Ideal.span_pair_eq_span_left_iff_dvd.mpr
    ⟨algebraMap K N c * middleNodeZ c, middleNode_v_multiple W₀ c⟩,
    middleNode_tIdeal W₀ c (D.a₁_unit.map (residue R))]

/-- The original opposite-slope line maps to the second ordered node's z-zero branch. -/
theorem residueSecondNodeMap_lineIdeal :
    Ideal.map (AlgHom.toRingHom G)
      (Ideal.span {t, v + algebraMap K T (WeierstrassCurve.a₁ W₀)}) =
        Ideal.span {middleNodeZ c} := by
  rw [Ideal.map_span, Set.image_pair]
  change Ideal.span {G t, G (v + algebraMap K T (WeierstrassCurve.a₁ W₀))} = _
  rw [map_add, AlgHom.commutes, residueSecondNodeMap_coord, residueSecondNodeMap_coord]
  change Ideal.span {middleNodeT (WeierstrassCurve.a₁ W₀) c,
    -middleNodeV (WeierstrassCurve.a₁ W₀) c - algebraMap K N (WeierstrassCurve.a₁ W₀) +
      algebraMap K N (WeierstrassCurve.a₁ W₀)} = _
  rw [sub_add_cancel, Ideal.span_pair_neg, Ideal.span_pair_eq_span_left_iff_dvd.mpr
    ⟨algebraMap K N c * middleNodeZ c, middleNode_v_multiple W₀ c⟩,
    middleNode_tIdeal W₀ c (D.a₁_unit.map (residue R))]

end FLT.Mazur.WeierstrassSuccessiveX
