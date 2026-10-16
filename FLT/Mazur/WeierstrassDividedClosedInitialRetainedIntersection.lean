/-
Copyright (c) 2026 krandder. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: krandder
-/
module

public import FLT.Mazur.WeierstrassDividedClosedInitialTriangleIntersection
public import FLT.Mazur.WeierstrassDividedPolygonInitialRetainedIntersection
public import FLT.Mazur.WeierstrassModificationXArithmeticIncidenceOpen

/-!
# Reflection of every original initial/retained intersection

The polygon label arithmetic forces the original first edge on the same
arm. The full D(p) preimage and original corrected boundary square then
recover equality in the source stage, excluding all nonadjacent pairs.
-/

@[expose] public noncomputable section
open AlgebraicGeometry CategoryTheory
namespace FLT.Mazur.WeierstrassDividedDepth
open PolygonArithmeticStages PolygonSmoothing WeierstrassModificationX
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
attribute [local irreducible] finiteGlobalModel finiteGlobalContraction
/-- Matching full overlap squares reflect a point equality whenever its first point lifts. -/
theorem fullChartOverlap_points_eq {S X Y Z U : Scheme}
    (a : X ⟶ S) (b : Y ⟶ S) (f : X ⟶ Z) (g : Y ⟶ Z) (l : U ⟶ X) (r : U ⟶ Y)
    (hs : l ≫ a = r ≫ b) (ht : l ≫ f = r ≫ g) (hg : Function.Injective g)
    (x : X) (y : Y) (hx : x ∈ Set.range l) (h : f x = g y) : a x = b y := by
  obtain ⟨z, rfl⟩ := hx
  have he := congrArg (fun m ↦ m z) ht
  have hy : r z = y := hg (he.symm.trans h)
  exact (congrArg (fun m ↦ m z) hs).trans (congrArg b hy)

section Preimage
variable {R : Type} [CommRing R]
  {W : WeierstrassCurve R} {π : R} {start n : ℕ}
  (data : (i : Fin (n + 1)) → Data W π (start + i.val))
  (H : ArithmeticAtlasCoefficients data) (m : ℕ)
local notation "Q" => Quotient R π m
local notation "d" => data (Fin.mk 0 (Nat.zero_lt_succ n))
local notation "τ" => arithmeticInitialMobiusSmoothing W H.a1_unit (π ^ start) π m
local notation "hn" => Fact.mk
  (arithmeticInitialFactorRatioSmoothing_nilpotent W H.a1_unit (π ^ start) π m H.scale_div)
local notation "N" => arithmeticInitialFactorRatioChart π m W (π ^ start)
  (Data.b3 d) (Data.b4 d) (Data.b6 d) H.a1_unit H.a2_div
    (H.b3_div _) (H.b4_div _) (H.b6_div _)
/-- The full normalized left puncture is the original arithmetic incidence overlap. -/
theorem arithmeticInitialFactorRatioChart_left_preimage :
    N ⁻¹' Set.range (leftBranchOpen Q τ) =
      Set.range (arithmeticInitialPunctureInclusion π m W (π ^ start)
        H.a1_unit H.scale_div) := by
  rw [arithmeticInitialPunctureInclusion_range]
  exact polynomialFactorRatioChart_left_preimage ..
end Preimage

attribute [local irreducible] arithmeticInitialFactorRatioChart
  arithmeticRetainedFixedSmoothingIso arithmeticInitialPunctureIso

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
local notation "τ" => arithmeticInitialMobiusSmoothing W H.a1_unit (π ^ 1) π 0
local notation "hn" => Fact.mk
  (arithmeticInitialFactorRatioSmoothing_nilpotent W H.a1_unit (π ^ 1) π 0 H.scale_div)
local notation "N" => arithmeticInitialFactorRatioChart π 0 W (π ^ 1)
  (Data.b3 d) (Data.b4 d) (Data.b6 d) H.a1_unit H.a2_div
    (H.b3_div _) (H.b4_div _) (H.b6_div _)
local notation "e" => twistedArithmeticAtlasIso hπ data H 0 j hj u hu
local notation "P" => arithmeticInitialPunctureInclusion π 0 W (π ^ 1)
  H.a1_unit H.scale_div
local notation "E" => arithmeticInitialPunctureIso π 0 W (π ^ 1)
  (Data.b3 d) (Data.b4 d) (Data.b6 d) H.a1_unit H.scale_div H.a2_div
    (H.b3_div _) (H.b4_div _) (H.b6_div _)
local notation "J" => Iso.inv (E) ≫ rightBranchOpen Q (parameter R π 0)

local notation "c" => @PolygonInfinitesimal.chart Q _ τ hn (2 * (j + 1) + 3)
  (Nat.le_trans (Nat.le_succ 2) (Nat.le_add_left 3 (2 * (j + 1))))
local notation "O" => fun (b : Bool) ↦
  ite (b = true) (Iso.hom (branchSwapIso Q τ)) (𝟙 (PolygonSmoothing.chart Q τ))

omit [IsBezout R] in
/-- The actual closed initial map has its full corrected oriented node formula. -/
theorem arithmeticClosedInitial_normalized (b : Bool) :
    G (.initial b) = N ≫ O b ≫ c (initialPolygonIndex (j + 1) b) := by
  let _ := hn
  exact arithmeticFactorRatioLabeledInitialMap_normalized data H hπ 0 (j + 1) hj b

omit [IsBezout R] in
/-- The actual retained comparison is its whole-chart isomorphism and prescribed label. -/
theorem arithmeticClosedRetained_normalized (idx : Fin (j + 1)) (b : Bool) :
    G (.retained idx b) = (e (.retained idx b)).hom ≫
      c (retainedPolygonIndex (j + 1) idx b) := by
  let _ := hn
  exact (twistedArithmeticRetained_polygon hπ data H 0 j hj u hu idx b).symm

attribute [local irreducible] arithmeticClosedPolygonComparisonChart

omit [IsBezout R] in
/-- The full target equality forces the original first label and incidence puncture. -/
theorem arithmeticClosedInitialRetained_location (idx : Fin (j + 1)) (b other : Bool)
    (x : Spec (.of (PolynomialNodeOpen (W.map (algebraMap R Q))
      (algebraMap R Q (π ^ 1))))) (y : PolygonSmoothing.chart Q (parameter R π 0))
    (h : G (.initial b) x = G (.retained idx other) y) :
    idx.val = 0 ∧ b = other ∧ x ∈ Set.range P := by
  let _ := hn
  have hx₀ := congrArg (fun f ↦ f x)
    (arithmeticClosedInitial_normalized hπ data H j hj u hu b)
  have hy₀ := congrArg (fun f ↦ f y)
    (arithmeticClosedRetained_normalized hπ data H j hj u hu idx other)
  have he := hx₀.symm.trans (h.trans hy₀)
  obtain ⟨hi, hb, hx⟩ := initialPolygon_retained_intersection Q τ (j + 1) idx b other
    (N x) ((e (.retained idx other)).hom y) he
  refine ⟨hi, hb, ?_⟩
  rw [← arithmeticInitialFactorRatioChart_left_preimage data H 0]
  exact hx

/-- Every original initial/retained equality comes from its actual full boundary. -/
theorem arithmeticClosedInitialRetained_points_eq (idx : Fin (j + 1)) (b other : Bool)
    (x : Spec (.of (PolynomialNodeOpen (W.map (algebraMap R Q))
      (algebraMap R Q (π ^ 1))))) (y : PolygonSmoothing.chart Q (parameter R π 0))
    (h : G (.initial b) x = G (.retained idx other) y) :
    a (.initial b) x = a (.retained idx other) y := by
  obtain ⟨hi, hb, hx⟩ :=
    arithmeticClosedInitialRetained_location hπ data H j hj u hu idx b other x y h
  have hi' : idx = ⟨0, Nat.zero_lt_succ j⟩ := Fin.ext hi
  subst idx
  subst other
  exact fullChartOverlap_points_eq (a (.initial b))
    (a (.retained ⟨0, Nat.zero_lt_succ j⟩ b)) (G (.initial b))
    (G (.retained ⟨0, Nat.zero_lt_succ j⟩ b)) P J
    (arithmeticLabeledAtlas_initial_edge_isPullback hπ data H 0 (j + 1) hj
      (Nat.zero_lt_succ j) b).w
    (arithmeticClosedPolygonComparisonChart_initial hπ data H j hj u hu b)
    (G (.retained ⟨0, Nat.zero_lt_succ j⟩ b)).isOpenEmbedding.injective x y hx h

end FLT.Mazur.WeierstrassDividedDepth
