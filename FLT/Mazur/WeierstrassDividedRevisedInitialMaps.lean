/-
Copyright (c) 2026 krandder. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: krandder
-/
module

public import FLT.Mazur.WeierstrassDividedRevisedExteriorEdges
public import FLT.Mazur.WeierstrassDividedArithmeticInitialPolygonImage

/-!
# Original full initial opens in the revised polygon

The polynomial factor ratio retains the complete initial open, its deleted
tangent divisor, and the infinity edge that covers its complement.
-/

@[expose] public noncomputable section
open AlgebraicGeometry CategoryTheory
namespace FLT.Mazur.WeierstrassDividedDepth
open PolygonArithmeticStages PolygonSmoothing WeierstrassModificationX
set_option backward.isDefEq.respectTransparency false
/-- A full node open missing only y = 1 is completed by its right puncture. -/
theorem revisedInitialNode_right_cover {S : Type} [CommRing S] (t : S)
    {X : Scheme} (f : X ⟶ PolygonSmoothing.chart S t)
    (hf : Set.range f = (PrimeSpectrum.basicOpen (rightCoordinate t - 1) :
      Set (PrimeSpectrum (ChartRing t)))) (x : PolygonSmoothing.chart S t) :
    x ∈ Set.range f ∨ x ∈ Set.range (rightBranchOpen S t) := by
  rw [hf, rightBranchOpen_range]
  change rightCoordinate t - 1 ∉ x.asIdeal ∨ rightCoordinate t ∉ x.asIdeal
  by_contra h
  obtain ⟨ha, hb⟩ := not_or.mp h
  have he : (1 : ChartRing t) ∈ x.asIdeal := by
    convert x.asIdeal.sub_mem (not_not.mp hb) (not_not.mp ha) using 1
    ring
  exact x.isPrime.ne_top (Ideal.eq_top_of_isUnit_mem x.asIdeal he isUnit_one)

/-- A cover of a node transports through any morphism without expanding that target. -/
theorem revisedNode_image_cover {U V X Y : Scheme} (f : U ⟶ X) (g : V ⟶ X)
    (c : X ⟶ Y) (h : ∀ x : X, x ∈ Set.range f ∨ x ∈ Set.range g) (x : X) :
    c x ∈ Set.range (f ≫ c) ∨ c x ∈ Set.range (g ≫ c) := by
  rcases h x with ⟨z, rfl⟩ | ⟨z, rfl⟩
  · exact Or.inl ⟨z, rfl⟩
  · exact Or.inr ⟨z, rfl⟩

variable {R : Type} [CommRing R] {W : WeierstrassCurve R} {π : R} {n : ℕ}
  (data : (i : Fin (n + 1)) → Data W π (1 + i.val))
  (H : ArithmeticAtlasCoefficients data) (m j : ℕ) (hj : j + 1 ≤ n)
  (u : Rˣ) (hu : (data ⟨j + 1, Nat.lt_succ_of_le hj⟩).b6 = π * ↑u)
local notation "Q" => Quotient R π m
local notation "q" => algebraMap R Q
local notation "d₀" => data (Fin.mk 0 (Nat.zero_lt_succ n))
local notation "τ" => arithmeticInitialMobiusSmoothing W H.a1_unit (π ^ 1) π m
local notation "N" => arithmeticInitialFactorRatioChart π m W (π ^ 1)
  (Data.b3 d₀) (Data.b4 d₀) (Data.b6 d₀) H.a1_unit H.a2_div
    (H.b3_div _) (H.b4_div _) (H.b6_div _)
local notation "O" => twistedRetainedOrientation data H m
local notation "c" => arithmeticRevisedPolygonInitialChart data H m j hj u hu

/-- Both original full initial opens map into their revised cyclic labels. -/
def arithmeticOriginalRevisedInitialMap (b : Bool) :
    Spec (.of (PolynomialNodeOpen (W.map q) (q (π ^ 1)))) ⟶
      arithmeticRevisedPolygon data H m j hj u hu :=
  N ≫ (O b).hom ≫ c b

local notation "f" => arithmeticOriginalRevisedInitialMap data H m j hj u hu

instance arithmeticOriginalRevisedInitialMap_isOpenImmersion (b : Bool) :
    IsOpenImmersion (f b) := by
  unfold arithmeticOriginalRevisedInitialMap
  infer_instance

attribute [local irreducible] arithmeticInitialFactorRatioChart
  arithmeticRevisedPolygonInitialChart twistedRetainedOrientation

/-- The revised initial image still records the exact deleted normalized tangent divisor. -/
theorem arithmeticOriginalRevisedInitialMap_range (b : Bool) :
    Set.range (f b) = ((O b).hom ≫ c b) ''
      (PrimeSpectrum.basicOpen (rightCoordinate τ - 1) : Set (PrimeSpectrum (ChartRing τ))) := by
  rw [arithmeticOriginalRevisedInitialMap]
  change Set.range (((O b).hom ≫ c b) ∘ N) = _
  rw [Set.range_comp, arithmeticInitialFactorRatioChart_image data H m]

/-- Each complete initial node is covered by the original initial open and its infinity edge. -/
theorem arithmeticOriginalRevisedInitialMap_edge_cover (b : Bool)
    (x : PolygonSmoothing.chart Q τ) :
    ((O b).hom ≫ c b) x ∈ Set.range (f b) ∨
      ((O b).hom ≫ c b) x ∈ Set.range (rightBranchOpen Q τ ≫ (O b).hom ≫ c b) := by
  rw [arithmeticOriginalRevisedInitialMap]
  exact revisedNode_image_cover N (rightBranchOpen Q τ) ((O b).hom ≫ c b)
    (revisedInitialNode_right_cover τ N (arithmeticInitialFactorRatioChart_image data H m)) x

end FLT.Mazur.WeierstrassDividedDepth
