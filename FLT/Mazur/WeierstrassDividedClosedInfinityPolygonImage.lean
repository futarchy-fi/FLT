/-
Copyright (c) 2026 krandder. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: krandder
-/
module

public import FLT.Mazur.WeierstrassSplitNodalInfinityFactorRatio
public import FLT.Mazur.WeierstrassDividedArithmeticFactorRatioLabeledMaps
public import FLT.Mazur.WeierstrassDividedClosedBoundaryUnits

/-!
# The actual closed arithmetic infinity label fills the polygon edge

The vanishing coefficient ideal identifies the entire regular infinity ratio
with a torus isomorphism. Transport through the original tensor chart gives
an open immersion whose image is the full prescribed polygon edge.
-/

@[expose] public noncomputable section
open AlgebraicGeometry CategoryTheory
namespace FLT.Mazur.WeierstrassDividedDepth
open PolygonArithmeticStages PolygonSmoothing WeierstrassModificationX WeierstrassIntegralChart
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
section Full
variable {R : Type} [CommRing R] (W : WeierstrassCurve R) (ha : IsUnit W.a₁)
  (s τ : R) [Fact (IsNilpotent τ)] (k : ℕ) (b3 : R) (r : Polynomial R)
  (I : Ideal R) (hI : IsNilpotent I) (hzero : I = ⊥)
  (hr : r ∈ I.map Polynomial.C) (hb : b3 ∈ I)
  (h2 : W.a₂ ∈ I) (h3 : W.a₃ ∈ I) (h4 : W.a₄ ∈ I) (h6 : W.a₆ ∈ I)
local notation "P" => infinityFactorRatioParameter W I hI h2 h3 h4 h6 s b3 r hr hb
local notation "F" => fullFactorRatioInfinityPolygonMap W s τ k b3 r I hI hr hb h2 h3 h4 h6
local notation "e" => rightBranchOpen R τ ≫
  PolygonInfinitesimal.chart R τ (2 * k + 3) (by omega) (initialPolygonIndex k false)

include ha hzero in
/-- Vanishing of the coefficient ideal makes the entire infinity comparison an open immersion. -/
theorem fullFactorRatioInfinityPolygonMap_isOpenImmersion_of_ideal_zero :
    IsOpenImmersion F := by
  let _ : IsIso P := infinityFactorRatioParameter_isIso_of_ideal_zero
    s W ha I hI hzero h2 h3 h4 h6 b3 r hr hb
  change IsOpenImmersion (P ≫ e)
  infer_instance

include ha hzero in
/-- No point of the full infinity edge is omitted when the coefficient ideal vanishes. -/
theorem fullFactorRatioInfinityPolygonMap_range_of_ideal_zero :
    Set.range F = Set.range e := by
  let _ : IsIso P := infinityFactorRatioParameter_isIso_of_ideal_zero
    s W ha I hI hzero h2 h3 h4 h6 b3 r hr hb
  have hs : Function.Surjective P := (Scheme.homeoOfIso (asIso P)).surjective
  change Set.range (e ∘ P) = _
  rw [Set.range_comp, hs.range_eq, Set.image_univ]
end Full

attribute [local irreducible] finiteGlobalModel finiteGlobalContraction
variable {R : Type} [CommRing R] [IsDomain R]
  {W : WeierstrassCurve R} {π : R} {start n : ℕ}
  (data : (i : Fin (n + 1)) → Data W π (start + i.val))
  (H : ArithmeticAtlasCoefficients data) (hπ : π ≠ 0) (k : ℕ) (hk : k ≤ n)
local notation "Q" => Quotient R π 0
local notation "τ" => arithmeticInitialMobiusSmoothing W H.a1_unit (π ^ start) π 0
local notation "hn" => Fact.mk
  (arithmeticInitialFactorRatioSmoothing_nilpotent W H.a1_unit (π ^ start) π 0 H.scale_div)
local notation "f" => arithmeticFactorRatioLabeledInfinityMap data H hπ 0 k hk
local notation "d" => data (Fin.mk 0 (Nat.zero_lt_succ n))
local notation "M" => arithmeticFactorRatioInfinityPolygonMap π 0 W (π ^ start)
  (Data.b3 d) (Data.b4 d) (Data.b6 d) H.a1_unit H.scale_div H.a2_div
  (H.b3_div _) (H.b4_div _) (H.b6_div _)
  (H.a3_div data) (H.a4_div data) (H.a6_div data) k
local notation "e" => rightBranchOpen Q τ ≫
  @PolygonInfinitesimal.chart Q _ τ hn (2 * k + 3) (by omega) (initialPolygonIndex k false)

/-- The entire original infinity label embeds at arithmetic order zero. -/
instance arithmeticClosedInfinityPolygonMap_isOpenImmersion : IsOpenImmersion f := by
  let _ := hn
  let _ : IsOpenImmersion M := by
    unfold arithmeticFactorRatioInfinityPolygonMap
    apply fullFactorRatioInfinityPolygonMap_isOpenImmersion_of_ideal_zero
      (ha := H.a1_unit.map (algebraMap R Q))
    simp [ideal, arithmeticClosedParameter_zero]
  change IsOpenImmersion ((arithmeticInfinityTensorIso π 0 W).inv ≫ M)
  infer_instance

/-- Its exact image is the whole original infinity edge, over R/(pi) itself. -/
theorem arithmeticClosedInfinityPolygonMap_range : Set.range f = Set.range e := by
  let _ := hn
  have hs : Function.Surjective (arithmeticInfinityTensorIso π 0 W).inv :=
    (Scheme.homeoOfIso (arithmeticInfinityTensorIso π 0 W).symm).surjective
  have he : Set.range ((arithmeticInfinityTensorIso π 0 W).inv ≫ M) = Set.range M := by
    change Set.range (M ∘ (arithmeticInfinityTensorIso π 0 W).inv) = _
    rw [Set.range_comp, hs.range_eq, Set.image_univ]
  have hz : Set.range M = Set.range e := by
    unfold arithmeticFactorRatioInfinityPolygonMap
    apply fullFactorRatioInfinityPolygonMap_range_of_ideal_zero
      (ha := H.a1_unit.map (algebraMap R Q))
    simp [ideal, arithmeticClosedParameter_zero]
  exact he.trans hz

end FLT.Mazur.WeierstrassDividedDepth
