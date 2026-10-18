/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.EquivalenceRelationBoundaryRankSeparation

/-!
# Nilpotence detected by the actual boundary rank stages

The matching stage maps onto exactly the complete part of the full scalar
boundary product. Surjectivity of that map detects nilpotence of the fixed
finite test ideal. Equivalently, every higher rank stage must be empty.
This uses pointwise detection of nilpotence, with no scheme descent assertion.
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
local instance rankDescentOver_etale : Etale (Over.mk p).hom := ‹Etale p›
local instance rankDescentOver_separated : IsSeparated (Over.mk p).hom := ‹IsSeparated p›
local instance rankDescentOver_compact : QuasiCompact (Over.mk p).hom := ‹QuasiCompact p›
local notation "ρ" => restrictedAction (action e (Fin n) o) U hU
local notation "b" => chartBoundaryEndpoint n o U e hU s κ
local notation "Z" => U.ι ⁻¹' completePointLocus («p» := p) («q» := q) (Fin n) o
local notation "tests" => completeAffineOrbitTests e (Fin n) o U hU
variable (k : ℕ)


omit [TopologicalSpace.NoetherianSpace U.toScheme] in
/-- The matching stage has exactly the complete image in the full original product. -/
theorem boundaryRank_matching_range :
    Set.range (boundaryRankProductMap n o U e hU s κ k n) =
      boundaryProjection s κ ⁻¹'
        (completeAffineOrbitImage e (Fin n) o U hU : Set (quotient ρ)) := by
  apply Set.Subset.antisymm
  · rintro _ ⟨y, rfl⟩
    exact boundaryRank_matching_complete n o U e hU s κ k y
  · intro z hz
    obtain ⟨x, hx⟩ := chartBoundaryProduct_surjective n o U e hU s κ z
    have he : quotientMap ρ (chartBoundaryChart n o U e hU s κ x) =
        boundaryProjection s κ (chartBoundaryProduct n o U e hU s κ x) :=
      congrArg (fun f ↦ f x) (pullback.condition
        (f := quotientMap ρ) (g := boundaryProjection s κ))
    have hc : chartBoundaryChart n o U e hU s κ x ∈ Z := by
      rw [← completeAffineOrbitImage_preimage e (Fin n) o U hU]
      change quotientMap ρ (chartBoundaryChart n o U e hU s κ x) ∈
        completeAffineOrbitImage e (Fin n) o U hU
      rw [he, hx]
      exact hz
    have hr : x ∈ Set.range (rankPullbackMap (Over.mk p) b n k) := by
      rw [rankPullbackMap_range]
      exact (chart_complete_iff_exactRank n o U _).mp hc
    obtain ⟨y, hy⟩ := hr
    refine ⟨y, ?_⟩
    change chartBoundaryProduct n o U e hU s κ
      (rankPullbackMap (Over.mk p) b n k y) = z
    rw [hy, hx]

attribute [local irreducible] boundaryRankProductMap chartBoundary
  chartBoundaryChart chartBoundaryProduct chartBoundaryEndpoint

/-- The finite ideal is nilpotent exactly when the matching stage covers the full product. -/
theorem boundaryTestIdeal_nilpotent_iff_matching_surjective :
    IsNilpotent (boundaryTestIdeal s κ tests) ↔
      Function.Surjective (boundaryRankProductMap n o U e hU s κ k n) := by
  rw [boundaryTestIdeal_nilpotent_iff]
  constructor
  · intro h z
    have hz : boundaryProjection s κ z ∈ completeAffineOrbitImage e (Fin n) o U hU := by
      apply (mem_closedOrbitImage_iff_tests ρ Z (completeChart_isClosed (Fin n) o U) _).mpr
      intro t ht
      have he := (Scheme.isNilpotent_iff_basicOpen_eq_bot _).mp (h t ht)
      rw [boundaryCoordinate_basicOpen] at he
      by_contra hn
      have hm : z ∈ boundaryProjection s κ ⁻¹ᵁ PrimeSpectrum.basicOpen t := hn
      rw [he] at hm
      exact hm
    have hr : z ∈ Set.range (boundaryRankProductMap n o U e hU s κ k n) := by
      rw [boundaryRank_matching_range]
      exact hz
    exact hr
  · intro h t ht
    rw [Scheme.isNilpotent_iff_basicOpen_eq_bot, boundaryCoordinate_basicOpen]
    apply eq_bot_iff.mpr
    intro z hz
    obtain ⟨y, rfl⟩ := h z
    exact hz ((mem_closedOrbitImage_iff_tests ρ Z
      (completeChart_isClosed (Fin n) o U) _).mp
        (boundaryRank_matching_complete n o U e hU s κ k y) t ht)

/-- Pointwise rank coverage suffices: precisely the higher stages obstruct nilpotence. -/
theorem boundaryTestIdeal_nilpotent_iff_higher_empty :
    IsNilpotent (boundaryTestIdeal s κ tests) ↔
      ∀ m : ℕ, n < m → IsEmpty (rankPullbackThickening (Over.mk p) b m k) := by
  rw [boundaryTestIdeal_nilpotent_iff_matching_surjective n o U e hU s κ k]
  constructor
  · intro h m hm
    refine ⟨fun y ↦ ?_⟩
    obtain ⟨x, hx⟩ := h (boundaryRankProductMap n o U e hU s κ k m y)
    have hc := boundaryRank_matching_complete n o U e hU s κ k x
    rw [hx] at hc
    exact boundaryRank_higher_not_complete n o U e hU s κ k m hm y hc
  · intro h z
    obtain ⟨m, y, hy⟩ := exists_boundary_rankThickening_lift n o U e hU s κ k z
    have hm : m = n := by
      rcases lt_trichotomy m n with hm | hm | hm
      · exact ((boundary_rankThickening_empty_below n o U e hU s κ m k hm).false y).elim
      · exact hm
      · exact ((h m hm).false y).elim
    subst m
    exact ⟨y, by simpa only [boundaryRankProductMap, Scheme.Hom.comp_apply] using hy⟩

end FLT.Mazur.EquivalenceRelationNormalizedFrames
