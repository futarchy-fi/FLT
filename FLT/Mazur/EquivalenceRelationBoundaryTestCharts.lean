/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.EquivalenceRelationBoundaryRankDescent
public import FLT.Mazur.AffineBoundaryTestThickenings

/-!
# Exact rank charts over the original test-ideal thickenings

Lift the full ideal-power test neighborhood to the original normalized chart.
Its endpoint has exact rank n everywhere. Higher rank thickenings are empty,
and a constructed surjective etale frame cover splits the original relation.
No claim that the test neighborhood covers the full boundary product is made.
-/

@[expose] public noncomputable section
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
namespace FLT.Mazur.EquivalenceRelationNormalizedFrames
open RelativeOrderedTuples AffineScalarBoundaryNilpotence
open FiniteGroupRestriction SchemeFiniteGroupQuotient
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
attribute [local irreducible] source action restrictedAction boundaryProduct boundaryCoordinate
  rankPullbackThickening rankPullbackMap
variable {D A : Scheme.{0}} {p q : D ⟶ A} [IsSeparated p] [Etale p]
  [QuasiCompact p] (n : ℕ) (o : Fin n) (U : (source p q (Fin n) o).Opens)
  (e : CategoryTheory.EquivalenceRelation p q)
  (hU : ∀ g : Equiv.Perm (Fin n), (action e (Fin n) o g).hom ⁻¹ᵁ U = U)
  [IsAffine U.toScheme] [TopologicalSpace.NoetherianSpace U.toScheme]
  {R T : Type} [CommRing R] [CommRing T]
  (s : R →+* invariantCoordinates (restrictedAction (action e (Fin n) o) U hU))
  (κ : R →+* T)
local instance testChartOver_etale : Etale (Over.mk p).hom := ‹Etale p›
local instance testChartOver_separated : IsSeparated (Over.mk p).hom := ‹IsSeparated p›
local instance testChartOver_compact : QuasiCompact (Over.mk p).hom := ‹QuasiCompact p›
local notation "ρ" => restrictedAction (action e (Fin n) o) U hU
local notation "b" => chartBoundaryEndpoint n o U e hU s κ
local notation "Z" => U.ι ⁻¹' completePointLocus («p» := p) («q» := q) (Fin n) o
local notation "tests" => completeAffineOrbitTests e (Fin n) o U hU
variable (k : ℕ)


/-- Lift the actual nonreduced test neighborhood to the original normalized chart. -/
def boundaryTestChart : Scheme :=
  pullback (quotientMap ρ)
    (boundaryTestThickeningMap s κ tests k ≫ boundaryProjection s κ)

/-- Retain the entire original test neighborhood, including its nilpotents. -/
def boundaryTestChartProjection :
    boundaryTestChart n o U e hU s κ k ⟶ boundaryTestThickening s κ tests k :=
  pullback.snd _ _

/-- The same chart lift retains the original endpoint in the full relation base. -/
def boundaryTestChartEndpoint : boundaryTestChart n o U e hU s κ k ⟶ A :=
  pullback.fst (quotientMap ρ)
    (boundaryTestThickeningMap s κ tests k ≫ boundaryProjection s κ) ≫
      U.ι ≫ first p q (Fin n) o

omit [QuasiCompact p] in
/-- Every point of the original test neighborhood has an actual chart lift. -/
theorem boundaryTestChartProjection_surjective :
    Function.Surjective (boundaryTestChartProjection n o U e hU s κ k) := by
  intro z
  obtain ⟨x, hx⟩ := (quotientMap ρ).surjective
    ((boundaryTestThickeningMap s κ tests k ≫ boundaryProjection s κ) z)
  exact (Scheme.Pullback.exists_preimage_pullback x z hx).imp fun _ h ↦ h.2

/-- Exact matching rank holds on this constructed scheme, without a rank assumption. -/
theorem boundaryTestChartEndpoint_exactRank (y : boundaryTestChart n o U e hU s κ k) :
    boundaryTestChartEndpoint n o U e hU s κ k y ∈ exactRank (Over.mk p) n := by
  let v := boundaryTestThickeningMap s κ tests k ≫ boundaryProjection s κ
  let x := pullback.fst (quotientMap ρ) v y
  let z := pullback.snd (quotientMap ρ) v y
  have he : quotientMap ρ x = v z :=
    congrArg (fun f ↦ f y) (pullback.condition (f := quotientMap ρ) (g := v))
  have ht : ∀ t ∈ tests, t ∈ (v z).asIdeal :=
    (mem_boundaryTestThickening_range s κ tests k _).mp
      (Set.mem_range_self (f := boundaryTestThickeningMap s κ tests k) z)
  have hc : x ∈ Z := by
    rw [← completeAffineOrbitImage_preimage e (Fin n) o U hU]
    change quotientMap ρ x ∈ completeAffineOrbitImage e (Fin n) o U hU
    rw [he]
    exact (mem_closedOrbitImage_iff_tests ρ Z (completeChart_isClosed (Fin n) o U) _).mpr ht
  exact (chart_complete_iff_exactRank n o U x).mp hc

attribute [local irreducible] boundaryTestChart boundaryTestChartProjection
  boundaryTestChartEndpoint
local notation "c" => boundaryTestChartEndpoint n o U e hU s κ k

/-- All higher original rank stages are absent over every order of this test neighborhood. -/
theorem boundaryTestChart_higher_empty (m l : ℕ) (hm : n < m) :
    IsEmpty (rankPullbackThickening (Over.mk p) c m l) := by
  refine ⟨fun y ↦ ?_⟩
  have hn := boundaryTestChartEndpoint_exactRank n o U e hU s κ k
    (rankPullbackMap (Over.mk p) c m l y)
  have hr := rankPullback_endpoint (Over.mk p) c m l y
  exact hn.2 (rankImageOpen_antitone (Over.mk p) hm hr.1)

/-- The constructed cover is surjective over the entire nonreduced chart lift. -/
theorem boundaryTestChart_frameCover_surjective :
    Function.Surjective (rankFrameProjection (Over.mk p) n c) := by
  apply rankFrameProjection_surjective
  rintro _ ⟨y, rfl⟩
  exact boundaryTestChartEndpoint_exactRank n o U e hU s κ k y

/-- This actual cover splits the full original relation with every coefficient retained. -/
def boundaryTestChartSplitIso :
    (∐ fun _ : Fin n ↦ rankFrameCover (Over.mk p) n c) ≅
      pullback p (rankFrameProjection (Over.mk p) n c ≫ c) :=
  rankFrameCoverIso (Over.mk p) n c (by
    rintro _ ⟨y, rfl⟩
    exact boundaryTestChartEndpoint_exactRank n o U e hU s κ k y)

/-- The earlier higher-rank stages vanish after actual base change to each test order. -/
theorem boundaryTest_higher_stage_empty (m l : ℕ) (hm : n < m) :
    IsEmpty (pullback (C := Scheme) (boundaryRankProductMap n o U e hU s κ l m)
      (boundaryTestThickeningMap s κ tests k)) := by
  refine ⟨fun w ↦ ?_⟩
  let r := boundaryRankProductMap n o U e hU s κ l m
  let t := boundaryTestThickeningMap s κ tests k
  let y := pullback.fst r t w
  let z := pullback.snd r t w
  have he : r y = t z :=
    congrArg (fun f ↦ f w) (pullback.condition (f := r) (g := t))
  obtain ⟨a, ha, hn⟩ := boundaryRank_higher_test n o U e hU s κ l m hm y
  have hz := (mem_boundaryTestThickening_range s κ tests k (t z)).mp
    (Set.mem_range_self (f := t) z) a ha
  change a ∉ (boundaryProjection s κ (r y)).asIdeal at hn
  rw [he] at hn
  exact hn hz

/-- At every pair of orders the original matching stage covers the full test neighborhood. -/
theorem boundaryTest_matching_stage_surjective (l : ℕ) :
    Function.Surjective (pullback.snd (boundaryRankProductMap n o U e hU s κ l n)
      (boundaryTestThickeningMap s κ tests k)) := by
  intro z
  have hz : z ∈ Set.range (pullback.snd (boundaryRankProductMap n o U e hU s κ l n)
      (boundaryTestThickeningMap s κ tests k)) := by
    rw [Scheme.Pullback.range_snd, boundaryRank_matching_range]
    apply (mem_closedOrbitImage_iff_tests ρ Z (completeChart_isClosed (Fin n) o U) _).mpr
    exact (mem_boundaryTestThickening_range s κ tests k _).mp
      (Set.mem_range_self (f := boundaryTestThickeningMap s κ tests k) z)
  exact hz

end FLT.Mazur.EquivalenceRelationNormalizedFrames
