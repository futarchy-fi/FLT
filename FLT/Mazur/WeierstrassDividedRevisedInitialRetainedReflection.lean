/-
Copyright (c) 2026 krandder. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: krandder
-/
module

public import FLT.Mazur.WeierstrassDividedRevisedInitialReflection
public import FLT.Mazur.WeierstrassDividedVariableInitialIntersection
public import FLT.Mazur.WeierstrassDividedClosedInitialRetainedIntersection
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
attribute [local irreducible] finiteGlobalModel finiteGlobalContraction
attribute [local irreducible] arithmeticInitialFactorRatioChart
  arithmeticRetainedFixedSmoothingIso arithmeticInitialPunctureIso

/-- Taking the morphism of an orientation choice preserves that choice. -/
theorem revisedOrientation_hom {X : Scheme} (e : X ≅ X) (b : Bool) :
    (if b then e else Iso.refl X).hom = if b then e.hom else 𝟙 X := by
  cases b <;> rfl

variable {R : Type} [CommRing R] [IsDomain R] [IsBezout R]
  {W : WeierstrassCurve R} {π : R} (hπ : π ≠ 0) {n : ℕ}
  (data : (i : Fin (n + 1)) → Data W π (1 + i.val))
  (H : ArithmeticAtlasCoefficients data) (j : ℕ) (hj : j + 1 ≤ n)
  (u : Rˣ) (hu : (data ⟨j + 1, Nat.lt_succ_of_le hj⟩).b6 = π * ↑u)
local notation "Q" => Quotient R π 1
local notation "d" => data (Fin.mk 0 (Nat.zero_lt_succ n))
local notation "A" => arithmeticLabeledAtlasObject hπ data H 1 (j + 1) hj
local notation "a" => arithmeticLabeledAtlasMap hπ data H 1 (j + 1) hj
local notation "G" => arithmeticFirstOriginalRevisedChart hπ data H j hj u hu
local notation "τ" => arithmeticInitialMobiusSmoothing W H.a1_unit (π ^ 1) π 1
local notation "hn" => Fact.mk
  (arithmeticInitialFactorRatioSmoothing_nilpotent W H.a1_unit (π ^ 1) π 1 H.scale_div)
local notation "N" => arithmeticInitialFactorRatioChart π 1 W (π ^ 1)
  (Data.b3 d) (Data.b4 d) (Data.b6 d) H.a1_unit H.a2_div
    (H.b3_div _) (H.b4_div _) (H.b6_div _)
local notation "C" => arithmeticRetainedFixedSmoothingIso data H 1 (j + 1) hj
local notation "K" => arithmeticFirstResidualRetainedIso hπ data H j hj u hu
local notation "O" => twistedRetainedOrientation data H 1
local notation "p" => arithmeticRevisedPolygonParameter data H 1 j hj u hu
local notation "c" => arithmeticRevisedPolygonInitialChart data H 1 j hj u hu
local notation "r" => arithmeticRevisedPolygonRetainedChart data H 1 j hj u hu
local notation "P" => arithmeticInitialPunctureInclusion π 1 W (π ^ 1)
  H.a1_unit H.scale_div
local notation "E" => arithmeticInitialPunctureIso π 1 W (π ^ 1)
  (Data.b3 d) (Data.b4 d) (Data.b6 d) H.a1_unit H.scale_div H.a2_div
    (H.b3_div _) (H.b4_div _) (H.b6_div _)
local notation "J" => Iso.inv (E) ≫ rightBranchOpen Q (parameter R π 1)

omit [IsBezout R] in
/-- The complete original initial map has its full factor-ratio node formula. -/
theorem arithmeticFirstRevisedInitial_normalized (b : Bool) :
    G (.initial b) = N ≫ (O b).hom ≫ c b := rfl

omit [IsBezout R] in
/-- The retained map includes its actual last-node correction before orientation. -/
theorem arithmeticFirstRevisedRetained_normalized (idx : Fin (j + 1)) (b : Bool) :
    G (.retained idx b) = (C idx).hom ≫
      (if idx.val = j then K b else Iso.refl _).hom ≫ (O b).hom ≫ r idx b := rfl

attribute [local irreducible] arithmeticFirstOriginalRevisedChart arithmeticRevisedPolygon
  PolygonVariableSmoothing.scheme PolygonVariableSmoothing.chartWithParameter
  arithmeticInitialMobiusSmoothing

omit [IsBezout R] in
/-- The full target equality forces the original first label and incidence puncture. -/
theorem arithmeticFirstRevisedInitialRetained_location (idx : Fin (j + 1)) (b other : Bool)
    (x : Spec (.of (PolynomialNodeOpen (W.map (algebraMap R Q))
      (algebraMap R Q (π ^ 1))))) (y : PolygonSmoothing.chart Q (parameter R π 1))
    (h : G (.initial b) x = G (.retained idx other) y) :
    idx.val = 0 ∧ b = other ∧ x ∈ Set.range P := by
  have hx₀ := congrArg (fun f ↦ f x)
    (arithmeticFirstRevisedInitial_normalized hπ data H j hj u hu b)
  have hy₀ := congrArg (fun f ↦ f y)
    (arithmeticFirstRevisedRetained_normalized hπ data H j hj u hu idx other)
  have he := hx₀.symm.trans (h.trans hy₀)
  simp only [Scheme.Hom.comp_apply, twistedRetainedOrientation, revisedOrientation_hom] at he
  obtain ⟨hi, hb, hx⟩ := variableInitial_retained_intersection Q (j + 1) τ p
    (fun b ↦ (arithmeticRevisedPolygonParameter_initial data H 1 j hj u hu b).symm)
    (fun idx b ↦ (arithmeticRevisedPolygonParameter_retained data H 1 j hj u hu idx b).symm)
    idx b other (N x)
    (((C idx).hom ≫ (if idx.val = j then K other else Iso.refl _).hom ≫ (O other).hom) y)
    (by
      simp only [Scheme.Hom.comp_apply, twistedRetainedOrientation, revisedOrientation_hom]
      convert he using 1
      unfold arithmeticRevisedPolygon arithmeticRevisedPolygonInitialChart
        arithmeticRevisedPolygonRetainedChart
      rfl)
  refine ⟨hi, hb, ?_⟩
  rw [← arithmeticInitialFactorRatioChart_left_preimage data H 1]
  exact hx

/-- Every original initial/retained equality comes from its actual full boundary. -/
theorem arithmeticFirstRevisedInitialRetained_points_eq (idx : Fin (j + 1)) (b other : Bool)
    (x : Spec (.of (PolynomialNodeOpen (W.map (algebraMap R Q))
      (algebraMap R Q (π ^ 1))))) (y : PolygonSmoothing.chart Q (parameter R π 1))
    (h : G (.initial b) x = G (.retained idx other) y) :
    a (.initial b) x = a (.retained idx other) y := by
  obtain ⟨hi, hb, hx⟩ :=
    arithmeticFirstRevisedInitialRetained_location hπ data H j hj u hu idx b other x y h
  have hi' : idx = ⟨0, Nat.zero_lt_succ j⟩ := Fin.ext hi
  subst idx
  subst other
  exact fullChartOverlap_points_eq (a (.initial b))
    (a (.retained ⟨0, Nat.zero_lt_succ j⟩ b)) (G (.initial b))
    (G (.retained ⟨0, Nat.zero_lt_succ j⟩ b)) P J
    (arithmeticLabeledAtlas_initial_edge_isPullback hπ data H 1 (j + 1) hj
      (Nat.zero_lt_succ j) b).w
    (arithmeticFirstOriginalRevisedChart_initial hπ data H j hj u hu b)
    (G (.retained ⟨0, Nat.zero_lt_succ j⟩ b)).isOpenEmbedding.injective x y hx h

end FLT.Mazur.WeierstrassDividedDepth
