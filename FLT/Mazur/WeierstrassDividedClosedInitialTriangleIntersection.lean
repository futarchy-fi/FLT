/-
Copyright (c) 2026 krandder. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: krandder
-/
module

public import FLT.Mazur.WeierstrassDividedClosedOppositeInfinityIntersection

/-!
# Equality reflection for the two original initial labels

The full corrected cross-label equation forces the original D(q) overlap.
The actual original overlap square then identifies the two source points.
-/

@[expose] public noncomputable section
open AlgebraicGeometry CategoryTheory
namespace FLT.Mazur.WeierstrassDividedDepth
open PolygonArithmeticStages PolygonSmoothing WeierstrassModificationX
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
attribute [local irreducible] finiteGlobalModel finiteGlobalContraction
section Preimage
variable {R : Type} [CommRing R] [IsDomain R]
  {W : WeierstrassCurve R} {π : R} {start n : ℕ}
  (data : (i : Fin (n + 1)) → Data W π (start + i.val))
  (H : ArithmeticAtlasCoefficients data) (hπ : π ≠ 0) (m k : ℕ) (hk : k ≤ n)
local notation "Q" => Quotient R π m
local notation "d" => data (Fin.mk 0 (Nat.zero_lt_succ n))
local notation "τ" => arithmeticInitialMobiusSmoothing W H.a1_unit (π ^ start) π m
local notation "hn" => Fact.mk
  (arithmeticInitialFactorRatioSmoothing_nilpotent W H.a1_unit (π ^ start) π m H.scale_div)
local notation "N" => arithmeticInitialFactorRatioChart π m W (π ^ start)
  (Data.b3 d) (Data.b4 d) (Data.b6 d) H.a1_unit H.a2_div
    (H.b3_div _) (H.b4_div _) (H.b6_div _)
local notation "c" => @PolygonInfinitesimal.chart Q _ τ hn (2 * k + 3)
  (Nat.le_trans (Nat.le_succ 2) (Nat.le_add_left 3 (2 * k)))
local notation "f" => arithmeticFactorRatioLabeledInitialMap data H hπ m k hk

/-- Cross-label equality forces the original full D(q) at every arithmetic order. -/
theorem arithmeticInitialPolygon_cross_preimage
    (x y : arithmeticLabeledAtlasObject hπ data H m k hk (.initial false))
    (h : f false x = f true y) :
    x ∈ Set.range (polynomialNodeOverlapInclusion (W.map (algebraMap R Q))
      (algebraMap R Q (π ^ start))) := by
  let _ := hn
  have hn' : initialPolygonIndex k false ≠ initialPolygonIndex k true := by
    intro he
    have := initialPolygonIndex_injective k he
    contradiction
  simp only [arithmeticFactorRatioLabeledInitialMap_normalized,
    Bool.false_eq_true, ↓reduceIte, Category.id_comp] at h
  change c (initialPolygonIndex k false) (N x) =
    c (initialPolygonIndex k true) ((branchSwapIso Q τ).hom (N y)) at h
  rcases (PolygonInfinitesimal.charts_eq_iff Q τ (2 * k + 3) (by omega) hn' _ _).mp h with
    ⟨z, hz, _, _⟩ | ⟨z, _, hx, _⟩
  · exact (initialPolygonIndex_not_reverse_preceding k hz).elim
  · rw [← arithmeticInitialFactorRatioChart_right_preimage π m W (π ^ start)
      (Data.b3 d) (Data.b4 d) (Data.b6 d) H.a1_unit H.a2_div
        (H.b3_div _) (H.b4_div _) (H.b6_div _)]
    exact ⟨(edgeInversion Q).hom z, hx⟩
end Preimage

variable {R : Type} [CommRing R] [IsDomain R] [IsBezout R]
  {W : WeierstrassCurve R} {π : R} (hπ : π ≠ 0) {n : ℕ}
  (data : (i : Fin (n + 1)) → Data W π (1 + i.val))
  (H : ArithmeticAtlasCoefficients data) (j : ℕ) (hj : j + 1 ≤ n)
  (u : Rˣ) (hu : (data ⟨j + 1, Nat.lt_succ_of_le hj⟩).b6 = π * ↑u)
local notation "Q" => Quotient R π 0
local notation "d" => data (Fin.mk 0 (Nat.zero_lt_succ n))
local notation "A" => arithmeticLabeledAtlasObject hπ data H 0 (j + 1) hj
local notation "a" => arithmeticLabeledAtlasMap hπ data H 0 (j + 1) hj
local notation "G" => arithmeticClosedPolygonComparisonChart hπ data H j hj u hu
local notation "P" => polynomialNodeOverlapInclusion
  (W.map (algebraMap R Q)) (algebraMap R Q (π ^ 1))
local notation "B" => arithmeticNodeOverlapOpposite π 0 W (π ^ 1)
  (Data.b3 d) (Data.b4 d) (Data.b6 d) H.a1_unit H.a2_div
    (H.b3_div _) (H.b4_div _) (H.b6_div _)
local notation "I" => arithmeticInitialOverlapToInfinity hπ data 0 (j + 1) hj
  H.a1_unit H.a2_div (H.b3_div _) (H.b4_div _) (H.b6_div _)

/-- The two full initial labels acquire no new equality in the closed polygon. -/
theorem arithmeticClosedInitialInitial_points_eq
    (x : A (.initial false)) (y : A (.initial true))
    (h : G (.initial false) x = G (.initial true) y) :
    a (.initial false) x = a (.initial true) y := by
  obtain ⟨z, rfl⟩ := arithmeticInitialPolygon_cross_preimage data H hπ 0 (j + 1) hj x y h
  have hc := arithmeticClosedPolygonComparisonChart_infinity hπ data H j hj u hu
  have ht := congrArg (fun g ↦ g z) (hc.1.symm.trans hc.2)
  have hy : B z = y := (G (.initial true)).isOpenEmbedding.injective (ht.symm.trans h)
  have hs := congrArg (fun g ↦ g z)
    (arithmeticLabeledAtlas_initial_isPullback hπ data H 0 (j + 1) hj).w
  exact hs.trans (congrArg (a (.initial true)) hy)

/-- Either original initial label reflects equality with the complete infinity chart. -/
theorem arithmeticClosedInitialInfinity_points_eq (b : Bool)
    (x : A (.initial b)) (y : A .infinity)
    (h : G (.initial b) x = G .infinity y) : a (.initial b) x = a .infinity y := by
  cases b
  · exact arithmeticClosedFirstInfinity_points_eq hπ data H j hj u hu x y h
  · exact arithmeticClosedOppositeInfinity_points_eq hπ data H j hj u hu x y h

end FLT.Mazur.WeierstrassDividedDepth
