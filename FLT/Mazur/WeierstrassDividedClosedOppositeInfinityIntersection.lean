/-
Copyright (c) 2026 krandder. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: krandder
-/
module

public import FLT.Mazur.WeierstrassDividedClosedFirstInfinityIntersection
public import FLT.Mazur.WeierstrassModificationXOppositeOverlapRange

/-!
# Reflection of the opposite initial/infinity intersection

The opposite original overlap leg fills the same standard puncture. Its
full corrected compatibility square recovers equality in the global stage.
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
  (H : ArithmeticAtlasCoefficients data) (hπ : π ≠ 0) (k : ℕ) (hk : k ≤ n) (b : Bool)
local notation "Q" => Quotient R π 0
local notation "d" => data (Fin.mk 0 (Nat.zero_lt_succ n))
local notation "τ" => arithmeticInitialMobiusSmoothing W H.a1_unit (π ^ start) π 0
local notation "hn" => Fact.mk
  (arithmeticInitialFactorRatioSmoothing_nilpotent W H.a1_unit (π ^ start) π 0 H.scale_div)
local notation "N" => arithmeticInitialFactorRatioChart π 0 W (π ^ start)
  (Data.b3 d) (Data.b4 d) (Data.b6 d) H.a1_unit H.a2_div
    (H.b3_div _) (H.b4_div _) (H.b6_div _)
local notation "O" => ite (b = true) (Iso.hom (branchSwapIso Q τ))
  (𝟙 (PolygonSmoothing.chart Q τ))
local notation "c" => @PolygonInfinitesimal.chart Q _ τ hn (2 * k + 3)
  (Nat.le_trans (Nat.le_succ 2) (Nat.le_add_left 3 (2 * k))) (initialPolygonIndex k b)

/-- Either oriented initial label pulls the full infinity edge back to standard D(q). -/
theorem arithmeticClosedInitialInfinity_standard_preimage :
    (arithmeticFactorRatioLabeledInitialMap data H hπ 0 k hk b) ⁻¹'
      Set.range (arithmeticFactorRatioLabeledInfinityMap data H hπ 0 k hk) =
        Set.range (polynomialNodeOverlapInclusion (W.map (algebraMap R Q))
          (algebraMap R Q (π ^ start))) := by
  let _ := hn
  have hi : Function.Injective (O ≫ c) := by
    cases b <;> simp only [Bool.false_eq_true, ↓reduceIte] <;>
      exact (Scheme.Hom.isOpenEmbedding _).injective
  rw [arithmeticClosedInfinityPolygonMap_range,
    ← initialPolygon_infinity_edge_range Q τ k b,
    arithmeticFactorRatioLabeledInitialMap_normalized]
  rw [← arithmeticInitialFactorRatioChart_right_preimage π 0 W (π ^ start)
    (Data.b3 d) (Data.b4 d) (Data.b6 d) H.a1_unit H.a2_div
      (H.b3_div _) (H.b4_div _) (H.b6_div _)]
  ext x
  constructor
  · rintro ⟨z, hz⟩
    exact ⟨z, hi hz⟩
  · rintro ⟨z, hz⟩
    exact ⟨z, congrArg (O ≫ c) hz⟩
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

/-- The closed comparison introduces no extra opposite-initial/infinity identifications. -/
theorem arithmeticClosedOppositeInfinity_points_eq (x : A (.initial true)) (y : A .infinity)
    (h : G (.initial true) x = G .infinity y) : a (.initial true) x = a .infinity y := by
  have hr : Set.range B = Set.range P := polynomialNodeOverlapOpposite_range ..
  have hx : x ∈ Set.range B := by
    rw [hr, ← arithmeticClosedInitialInfinity_standard_preimage data H hπ (j + 1) hj true]
    exact ⟨y, h.symm⟩
  obtain ⟨z, rfl⟩ := hx
  have ht := congrArg (fun g ↦ g z)
    (arithmeticClosedPolygonComparisonChart_infinity hπ data H j hj u hu).2
  have hy : I z = y := (G .infinity).isOpenEmbedding.injective (ht.trans h)
  have hs := congrArg (fun g ↦ g z)
    (arithmeticLabeledAtlas_opposite_infinity_isPullback hπ data H 0 (j + 1) hj).w
  exact hs.symm.trans (congrArg (a .infinity) hy)

end FLT.Mazur.WeierstrassDividedDepth
