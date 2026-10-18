/-
Copyright (c) 2026 krandder. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: krandder
-/
module

public import FLT.Mazur.WeierstrassDividedRevisedInfinityIntersection
public import FLT.Mazur.WeierstrassDividedRevisedInitialIntersection

/-!
# The two original initial labels reflect their full intersection

The independent target's full initial fiber product is its Laurent edge.
The exact factor-ratio preimage recovers the original initial overlap.
-/

@[expose] public noncomputable section
open AlgebraicGeometry CategoryTheory Limits
namespace FLT.Mazur.WeierstrassDividedDepth
open PolygonArithmeticStages PolygonSmoothing WeierstrassModificationX
set_option backward.isDefEq.respectTransparency false
/-- Equality in an actual fiber-product square forces the second point onto its full overlap. -/
theorem revisedComparison_pullback_preimage {S U V Y : Scheme}
    {l : S ⟶ U} {r : S ⟶ V} {f : U ⟶ Y} {g : V ⟶ Y}
    (hp : IsPullback l r f g) {x : U} {y : V} (h : f x = g y) :
    y ∈ Set.range r := by
  obtain ⟨z, _, hz⟩ := Scheme.exists_preimage_of_isPullback hp x y h
  exact ⟨z, hz⟩

section Target
variable {R : Type} [CommRing R] {W : WeierstrassCurve R} {π : R} {n : ℕ}
  (data : (i : Fin (n + 1)) → Data W π (1 + i.val))
  (H : ArithmeticAtlasCoefficients data) (m j : ℕ) (hj : j + 1 ≤ n)
  (u : Rˣ) (hu : (data ⟨j + 1, Nat.lt_succ_of_le hj⟩).b6 = π * ↑u)
local notation "Q" => Quotient R π m
local notation "N" => 2 * (j + 1) + 3
local notation "p" => arithmeticRevisedPolygonParameter data H m j hj u hu
local notation "τ" => arithmeticInitialMobiusSmoothing W H.a1_unit (π ^ 1) π m
local notation "c" => arithmeticRevisedPolygonInitialChart data H m j hj u hu
local notation "d₀" => data (Fin.mk 0 (Nat.zero_lt_succ n))
local notation "f" => arithmeticOriginalRevisedInitialMap data H m j hj u hu

attribute [local irreducible] arithmeticRevisedPolygon
  arithmeticRevisedPolygonInitialChart arithmeticInitialFactorRatioChart
local notation "F₀" => arithmeticInitialFactorRatioChart π m W (π ^ 1)
  (Data.b3 d₀) (Data.b4 d₀) (Data.b6 d₀) H.a1_unit H.a2_div
    (H.b3_div _) (H.b4_div _) (H.b6_div _)

/-- Cross-label equality forces the actual original D(q), without removing nilpotents. -/
theorem arithmeticOriginalRevisedInitial_cross_preimage
    (x y : Spec (.of (PolynomialNodeOpen (W.map (algebraMap R Q))
      (algebraMap R Q (π ^ 1))))) (h : f false x = f true y) :
    x ∈ Set.range (polynomialNodeOverlapInclusion (W.map (algebraMap R Q))
      (algebraMap R Q (π ^ 1))) := by
  simp only [arithmeticOriginalRevisedInitialMap, twistedRetainedOrientation,
    Bool.false_eq_true, ↓reduceIte, Iso.refl_hom, Category.id_comp] at h
  have hz : F₀ x ∈ Set.range (precedingBranch Q τ) :=
    revisedComparison_pullback_preimage
      (arithmeticRevisedPolygon_initial_isPullback data H m j hj u hu) h.symm
  rw [← arithmeticInitialFactorRatioChart_right_preimage π m W (π ^ 1)
    (Data.b3 d₀) (Data.b4 d₀) (Data.b6 d₀) H.a1_unit H.a2_div
      (H.b3_div _) (H.b4_div _) (H.b6_div _)]
  rw [precedingBranch_range] at hz
  exact hz
end Target

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
local notation "B" => arithmeticNodeOverlapOpposite π 1 W (π ^ 1)
  (Data.b3 d₀) (Data.b4 d₀) (Data.b6 d₀) H.a1_unit H.a2_div
    (H.b3_div _) (H.b4_div _) (H.b6_div _)

/-- The two complete initial labels acquire no extra point identification in the revised polygon. -/
theorem arithmeticFirstRevisedInitialInitial_points_eq
    (x : A (.initial false)) (y : A (.initial true))
    (h : G (.initial false) x = G (.initial true) y) :
    a (.initial false) x = a (.initial true) y := by
  have hx := arithmeticOriginalRevisedInitial_cross_preimage data H 1 j hj u hu x y h
  have hc := arithmeticFirstOriginalRevisedChart_infinity hπ data H j hj u hu
  exact revisedComparison_points_eq_of_overlap _ B _ _ _ _
    (arithmeticLabeledAtlas_initial_isPullback hπ data H 1 (j + 1) hj).w
    (hc.1.symm.trans hc.2).symm hx h

end FLT.Mazur.WeierstrassDividedDepth
