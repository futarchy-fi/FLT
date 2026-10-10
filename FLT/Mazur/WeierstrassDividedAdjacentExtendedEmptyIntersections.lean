/-
Copyright (c) 2026 krandder. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: krandder
-/
module

public import FLT.Mazur.WeierstrassDividedAdjacentParameterIntersection
public import FLT.Mazur.WeierstrassDividedAdjacentCrossedIntersection
public import FLT.Mazur.WeierstrassDividedAdjacentSectionSeparation
public import FLT.Mazur.WeierstrassDividedResidueAtlasExtension
public import FLT.Mazur.SchemeDisjointBaseChange

/-!
# Positive-depth crossed branches and excluded nodes remain disjoint after extension

Each result uses the actual global coefficient extension and the full original
maps. The crossed component and node/chart fiber products are empty schemes.
-/

@[expose] public noncomputable section
open AlgebraicGeometry CategoryTheory IsLocalRing Limits
namespace FLT.Mazur.WeierstrassDividedDepth
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
universe u
variable {R : Type u} [CommRing R] [IsDomain R] [IsBezout R] [IsLocalRing R]
  {W : WeierstrassCurve R} {π : R} (hπ : π ≠ 0) {start n depth : ℕ}
  (data : (i : Fin (n + 1)) → Data W π (start + i.val))
  (D : SplitNodeDepth W π depth) (j : ℕ) (hj : j + 1 ≤ n)
  (hk0 : 0 < start + j) (hk : 2 * (start + j + 1) ≤ depth)
  (hjNext : j + 2 ≤ n) (hkNext : 2 * (start + (j + 1) + 1) ≤ depth)
  (r : ℕ) (hr : j + 2 + r ≤ n)
variable (S : Type u) [CommRing S] [Algebra R S] [Algebra (ResidueField R) S]
  [IsScalarTower R (ResidueField R) S]
local notation "K" => ResidueField R
local notation "ext" => globalResidueExtensionMap hπ data S (j + 2 + r) hr
local notation "A₁" => adjacentRetainedFirstParameter hπ data D j hj hk0 hk r hr
local notation "A₂" => adjacentRetainedSecondParameter hπ data D j hj hk0 hk r hr
local notation "G₁" => olderGlobalMiddleFirstLine hπ data D (j + 1) hjNext r hr (by omega) hkNext
local notation "G₂" => olderGlobalMiddleSecondLine hπ data D (j + 1) hjNext r hr (by omega) hkNext
local notation "N₁" => adjacentRetainedFirstSection hπ data D j hj hk0 hk r hr
local notation "N₂" => adjacentRetainedSecondSection hπ data D j hj hk0 hk r hr
local notation "gNext" => olderGlobalTensorChart hπ data K (j + 1) hjNext r hr

/-- The first full parameter still misses the entire opposite line after extension. -/
theorem adjacentExtendedFirstParameter_cross_disjoint :
    Disjoint (Set.range (pullback.fst ext A₁)) (Set.range (pullback.fst ext G₂)) :=
  SchemeDisjointBaseChange.disjoint
    (adjacentRetainedFirstParameter_cross_disjoint hπ data D j hj hk0 hk hjNext hkNext r hr) ext

/-- The first crossed fiber product is the empty scheme after coefficient extension. -/
theorem adjacentExtendedFirstParameter_cross_isPullback :
    IsPullback (Scheme.emptyTo _) (Scheme.emptyTo _)
      (pullback.fst ext A₁) (pullback.fst ext G₂) :=
  SchemeDisjointBaseChange.isPullback
    (adjacentRetainedFirstParameter_cross_disjoint hπ data D j hj hk0 hk hjNext hkNext r hr) ext

/-- The second full parameter still misses the entire opposite line after extension. -/
theorem adjacentExtendedSecondParameter_cross_disjoint :
    Disjoint (Set.range (pullback.fst ext A₂)) (Set.range (pullback.fst ext G₁)) :=
  SchemeDisjointBaseChange.disjoint
    (adjacentRetainedSecondParameter_cross_disjoint hπ data D j hj hk0 hk hjNext hkNext r hr) ext

/-- The second crossed fiber product is the empty scheme after coefficient extension. -/
theorem adjacentExtendedSecondParameter_cross_isPullback :
    IsPullback (Scheme.emptyTo _) (Scheme.emptyTo _)
      (pullback.fst ext A₂) (pullback.fst ext G₁) :=
  SchemeDisjointBaseChange.isPullback
    (adjacentRetainedSecondParameter_cross_disjoint hπ data D j hj hk0 hk hjNext hkNext r hr) ext

/-- The retained first node stays outside the entire next extended chart. -/
theorem adjacentExtendedFirstSection_next_disjoint :
    Disjoint (Set.range (pullback.fst ext N₁)) (Set.range (pullback.fst ext gNext)) :=
  SchemeDisjointBaseChange.disjoint
    (adjacentRetainedFirstSection_next_disjoint hπ data D j hj hk0 hk hjNext r hr) ext

/-- The full extended first-node and next-chart fiber product is empty. -/
theorem adjacentExtendedFirstSection_next_isPullback :
    IsPullback (Scheme.emptyTo _) (Scheme.emptyTo _)
      (pullback.fst ext N₁) (pullback.fst ext gNext) :=
  SchemeDisjointBaseChange.isPullback
    (adjacentRetainedFirstSection_next_disjoint hπ data D j hj hk0 hk hjNext r hr) ext

/-- The retained second node stays outside the entire next extended chart. -/
theorem adjacentExtendedSecondSection_next_disjoint :
    Disjoint (Set.range (pullback.fst ext N₂)) (Set.range (pullback.fst ext gNext)) :=
  SchemeDisjointBaseChange.disjoint
    (adjacentRetainedSecondSection_next_disjoint hπ data D j hj hk0 hk hjNext r hr) ext

/-- The full extended second-node and next-chart fiber product is empty. -/
theorem adjacentExtendedSecondSection_next_isPullback :
    IsPullback (Scheme.emptyTo _) (Scheme.emptyTo _)
      (pullback.fst ext N₂) (pullback.fst ext gNext) :=
  SchemeDisjointBaseChange.isPullback
    (adjacentRetainedSecondSection_next_disjoint hπ data D j hj hk0 hk hjNext r hr) ext

end FLT.Mazur.WeierstrassDividedDepth
