/-
Copyright (c) 2026 krandder. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: krandder
-/
module

public import FLT.Mazur.WeierstrassSuccessiveXResidueNodeGeometry
public import FLT.Mazur.WeierstrassSuccessiveXMiddleConic

/-!
# Disjoint original residue node neighborhoods when the divided constant vanishes

The tensor slope relation makes the product of the two original tangent
functions zero. Their full principal neighborhoods therefore have empty
scheme intersection, which gives compatibility for arbitrary target maps.
-/

@[expose] public noncomputable section
open IsLocalRing AlgebraicGeometry CategoryTheory Limits
namespace FLT.Mazur.WeierstrassSuccessiveX
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
universe u
variable {R : Type u} [CommRing R] [IsDomain R] [IsLocalRing R]
  {W : WeierstrassCurve R} {π : R} {n : ℕ} (D : SplitNodeDepth W π n)
  (k : ℕ) (hk0 : 0 < k) (hk : 2 * (k + 1) ≤ n) (b3 b4 b6 : R)
  (h3 : W.a₃ = π ^ (k + 1) * b3) (h4 : W.a₄ = π ^ (k + 1) * b4)
  (hc : residue R b6 = 0)
local notation "K" => ResidueField R
local notation "T" => ScalarExtension W (π ^ k) π b3 b4 b6 K
local notation "v" => tensorCoord W (π ^ k) π b3 b4 b6 K 1
local notation "d" => v + algebraMap K T (residue R W.a₁)
local notation "f" => residueMiddleFirstNodeChart D k hk0 hk b3 b4 b6 h3 h4
local notation "g" => residueMiddleSecondNodeChart D k hk0 hk b3 b4 b6 h3 h4

include D hk0 hk h3 h4 hc in
/-- The two actual tensor tangent functions have zero product at strict depth. -/
theorem residue_middle_zero_tangent_product : v * d = 0 := by
  apply (residueRetainedFiberEquiv D k hk0 hk b3 b4 b6 h3 h4).injective
  simp only [map_mul, map_add, residueRetainedFiberEquiv_coord, AlgEquiv.commutes, map_zero]
  have H := middle_conic_relation (W.map (residue R)) (residue R b6)
    ((residue_eq_zero_iff _).mpr D.a₂_mem)
  simpa only [hc, map_zero, zero_mul, sub_zero, WeierstrassCurve.map_a₁] using H

include hc in
/-- The full original ordered tangent node neighborhoods are disjoint. -/
theorem residueMiddleZeroNodeCharts_disjoint : Disjoint (Set.range f) (Set.range g) := by
  rw [residueMiddleFirstNodeChart_range, residueMiddleSecondNodeChart_range]
  apply Set.disjoint_left.mpr
  intro p hp hq
  change d ∉ p.asIdeal at hp
  change -v ∉ p.asIdeal at hq
  have hz : v * d ∈ p.asIdeal := by
    rw [residue_middle_zero_tangent_product D k hk0 hk b3 b4 b6 h3 h4 hc]
    exact p.asIdeal.zero_mem
  rcases p.isPrime.mem_or_mem hz with hv | hd
  · exact hq (p.asIdeal.neg_mem hv)
  · exact hp hd

include hc in
/-- The categorical intersection itself is empty, including its full scheme structure. -/
theorem residueMiddleZeroNodePullback_isEmpty : IsEmpty (pullback f g : Scheme.{u}) :=
  Scheme.isEmpty_pullback _ _
    (residueMiddleZeroNodeCharts_disjoint D k hk0 hk b3 b4 b6 h3 h4 hc)

include hc in
/-- Any two target maps agree as morphisms on the actual empty node intersection. -/
theorem residueMiddleZeroNodeMaps_compatible {Y : Scheme.{u}}
    (a b : Spec (.of (MiddleNodeOpen (residue R b6))) ⟶ Y) :
    pullback.fst f g ≫ a = pullback.snd f g ≫ b := by
  let _ := residueMiddleZeroNodePullback_isEmpty D k hk0 hk b3 b4 b6 h3 h4 hc
  apply (cancel_epi (Scheme.emptyTo (pullback f g))).mp
  exact Scheme.empty_ext _ _

end FLT.Mazur.WeierstrassSuccessiveX
