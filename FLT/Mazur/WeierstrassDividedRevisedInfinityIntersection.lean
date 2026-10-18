/-
Copyright (c) 2026 krandder. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: krandder
-/
module

public import FLT.Mazur.WeierstrassDividedRevisedLocalIso
public import FLT.Mazur.WeierstrassDividedArithmeticAffinePolygonEmbedding
public import FLT.Mazur.WeierstrassModificationXOppositeOverlapRange

/-!
# Reflection of both complete original initial/infinity intersections

The full infinity image pulls back to the original D(q) at every order.
At first order the actual original overlap squares then reflect point equality.
-/

@[expose] public noncomputable section
open AlgebraicGeometry CategoryTheory
namespace FLT.Mazur.WeierstrassDividedDepth
open PolygonArithmeticStages PolygonSmoothing WeierstrassModificationX
set_option backward.isDefEq.respectTransparency false
/-- An embedded target cancels from an intersection preimage. -/
theorem revisedComparison_preimage_range {U V X Y : Scheme} (f : U ⟶ X) (g : V ⟶ X)
    (c : X ⟶ Y) [IsOpenImmersion c] :
    (f ≫ c) ⁻¹' Set.range (g ≫ c) = f ⁻¹' Set.range g := by
  ext x
  constructor
  · rintro ⟨z, hz⟩
    exact ⟨z, c.isOpenEmbedding.injective hz⟩
  · rintro ⟨z, hz⟩
    exact ⟨z, congrArg c hz⟩

/-- An actual overlap square reflects equality when the second chart embeds. -/
theorem revisedComparison_points_eq_of_overlap {S U V X Y : Scheme}
    (i : S ⟶ U) (j : S ⟶ V) (a : U ⟶ X) (b : V ⟶ X)
    (f : U ⟶ Y) (g : V ⟶ Y) [IsOpenImmersion g]
    (hs : i ≫ a = j ≫ b) (ht : j ≫ g = i ≫ f)
    {x : U} {y : V} (hx : x ∈ Set.range i) (h : f x = g y) : a x = b y := by
  obtain ⟨z, rfl⟩ := hx
  have hy : j z = y := g.isOpenEmbedding.injective
    ((congrArg (fun k ↦ k z) ht).trans h)
  exact (congrArg (fun k ↦ k z) hs).trans (congrArg b hy)

section Preimage
variable {R : Type} [CommRing R] {W : WeierstrassCurve R} {π : R} {n : ℕ}
  (data : (i : Fin (n + 1)) → Data W π (1 + i.val))
  (H : ArithmeticAtlasCoefficients data) (m j : ℕ) (hj : j + 1 ≤ n)
  (u : Rˣ) (hu : (data ⟨j + 1, Nat.lt_succ_of_le hj⟩).b6 = π * ↑u)
local notation "Q" => Quotient R π m
local notation "d₀" => data (Fin.mk 0 (Nat.zero_lt_succ n))
local notation "O" => twistedRetainedOrientation data H m
local notation "c" => arithmeticRevisedPolygonInitialChart data H m j hj u hu

/-- Both complete initial labels pull the full infinity edge back to the original puncture. -/
theorem arithmeticOriginalRevisedInitialInfinity_preimage (b : Bool) :
    (arithmeticOriginalRevisedInitialMap data H m j hj u hu b) ⁻¹'
      Set.range (arithmeticOriginalRevisedTensorInfinityMap data H m j hj u hu) =
        Set.range (polynomialNodeOverlapInclusion (W.map (algebraMap R Q))
          (algebraMap R Q (π ^ 1))) := by
  rw [arithmeticOriginalRevisedTensorInfinityMap_range,
    ← arithmeticRevisedPolygon_infinity_range data H m j hj u hu b,
    arithmeticOriginalRevisedInitialMap]
  rw [← arithmeticInitialFactorRatioChart_right_preimage π m W (π ^ 1)
    (Data.b3 d₀) (Data.b4 d₀) (Data.b6 d₀) H.a1_unit H.a2_div
      (H.b3_div _) (H.b4_div _) (H.b6_div _)]
  exact revisedComparison_preimage_range _ _ ((O b).hom ≫ c b)

end Preimage

attribute [local irreducible] finiteGlobalModel finiteGlobalContraction
variable {R : Type} [CommRing R] [IsDomain R] [IsBezout R]
  {W : WeierstrassCurve R} {π : R} (hπ : π ≠ 0) {n : ℕ}
  (data : (i : Fin (n + 1)) → Data W π (1 + i.val))
  (H : ArithmeticAtlasCoefficients data) (j : ℕ) (hj : j + 1 ≤ n)
  (u : Rˣ) (hu : (data ⟨j + 1, Nat.lt_succ_of_le hj⟩).b6 = π * ↑u)
local notation "Q" => Quotient R π 1
local notation "d₀" => data (Fin.mk 0 (Nat.zero_lt_succ n))
local notation "A" => arithmeticLabeledAtlasObject hπ data H 1 (j + 1) hj
local notation "a" => arithmeticLabeledAtlasMap hπ data H 1 (j + 1) hj
local notation "G" => arithmeticFirstOriginalRevisedChart hπ data H j hj u hu
local notation "P" => polynomialNodeOverlapInclusion
  (W.map (algebraMap R Q)) (algebraMap R Q (π ^ 1))
local notation "B" => arithmeticNodeOverlapOpposite π 1 W (π ^ 1)
  (Data.b3 d₀) (Data.b4 d₀) (Data.b6 d₀) H.a1_unit H.a2_div
    (H.b3_div _) (H.b4_div _) (H.b6_div _)
local notation "I" => arithmeticInitialOverlapToInfinity hπ data 1 (j + 1) hj
  H.a1_unit H.a2_div (H.b3_div _) (H.b4_div _) (H.b6_div _)

/-- The original first initial label and full infinity chart acquire no new equality. -/
theorem arithmeticFirstRevisedFirstInfinity_points_eq (x : A (.initial false)) (y : A .infinity)
    (h : G (.initial false) x = G .infinity y) : a (.initial false) x = a .infinity y := by
  have hx : x ∈ Set.range P := by
    rw [← arithmeticOriginalRevisedInitialInfinity_preimage data H 1 j hj u hu false]
    exact ⟨y, h.symm⟩
  exact revisedComparison_points_eq_of_overlap P I _ _ _ _
    (arithmeticLabeledAtlas_first_infinity_isPullback hπ data H 1 (j + 1) hj).w.symm
    (arithmeticFirstOriginalRevisedChart_infinity hπ data H j hj u hu).1 hx h

/-- The opposite initial label also reflects equality with the full infinity chart. -/
theorem arithmeticFirstRevisedOppositeInfinity_points_eq
    (x : A (.initial true)) (y : A .infinity)
    (h : G (.initial true) x = G .infinity y) : a (.initial true) x = a .infinity y := by
  have hr : Set.range B = Set.range P := polynomialNodeOverlapOpposite_range ..
  have hx : x ∈ Set.range B := by
    rw [hr, ← arithmeticOriginalRevisedInitialInfinity_preimage data H 1 j hj u hu true]
    exact ⟨y, h.symm⟩
  exact revisedComparison_points_eq_of_overlap B I _ _ _ _
    (arithmeticLabeledAtlas_opposite_infinity_isPullback hπ data H 1 (j + 1) hj).w.symm
    (arithmeticFirstOriginalRevisedChart_infinity hπ data H j hj u hu).2 hx h

/-- Either full original initial label reflects its infinity intersection. -/
theorem arithmeticFirstRevisedInitialInfinity_points_eq (b : Bool)
    (x : A (.initial b)) (y : A .infinity)
    (h : G (.initial b) x = G .infinity y) : a (.initial b) x = a .infinity y := by
  cases b
  · exact arithmeticFirstRevisedFirstInfinity_points_eq hπ data H j hj u hu x y h
  · exact arithmeticFirstRevisedOppositeInfinity_points_eq hπ data H j hj u hu x y h

end FLT.Mazur.WeierstrassDividedDepth
