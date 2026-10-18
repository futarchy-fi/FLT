/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.EquivalenceRelationBoundaryRankThickenings
public import FLT.Mazur.AffineBoundaryTestIdeal

/-!
# Constructed boundary equations on the matching rank thickenings

On every compact coefficient scheme mapping to a matching rank stage, the
original completeness tests are nilpotent. Their finite ideal has a vanishing
power. This constructs equations with all stage nilpotents retained; it does
not assert that these equations descend from the rank stages to the full product.
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
local instance rankEquationsOver_etale : Etale (Over.mk p).hom := ‹Etale p›
local instance rankEquationsOver_separated : IsSeparated (Over.mk p).hom := ‹IsSeparated p›
local instance rankEquationsOver_compact : QuasiCompact (Over.mk p).hom := ‹QuasiCompact p›
local notation "ρ" => restrictedAction (action e (Fin n) o) U hU
local notation "b" => chartBoundaryEndpoint n o U e hU s κ
local notation "Z" => U.ι ⁻¹' completePointLocus («p» := p) («q» := q) (Fin n) o
local notation "tests" => completeAffineOrbitTests e (Fin n) o U hU
variable (k : ℕ)

/-- The actual original product map of an ideal-power rank stage. -/
def boundaryRankProductMap (m : ℕ) :
    rankPullbackThickening (Over.mk p) b m k ⟶ boundaryProduct s κ :=
  rankPullbackMap (Over.mk p) b m k ≫ chartBoundaryProduct n o U e hU s κ

omit [TopologicalSpace.NoetherianSpace U.toScheme] in
/-- The matching stage lies over the actual closed complete orbit image. -/
theorem boundaryRank_matching_complete (y : rankPullbackThickening (Over.mk p) b n k) :
    boundaryProjection s κ (boundaryRankProductMap n o U e hU s κ k n y) ∈
      completeAffineOrbitImage e (Fin n) o U hU := by
  let x := rankPullbackMap (Over.mk p) b n k y
  have hr := rankPullback_endpoint (Over.mk p) b n k y
  have hc : chartBoundaryChart n o U e hU s κ x ∈ Z :=
    (chart_complete_iff_exactRank n o U _).mpr hr
  have he : quotientMap ρ (chartBoundaryChart n o U e hU s κ x) =
      boundaryProjection s κ (chartBoundaryProduct n o U e hU s κ x) :=
    congrArg (fun f ↦ f x) (pullback.condition
      (f := quotientMap ρ) (g := boundaryProjection s κ))
  exact ⟨chartBoundaryChart n o U e hU s κ x, hc, he⟩

attribute [local irreducible] boundaryRankProductMap chartBoundary
  chartBoundaryChart chartBoundaryProduct chartBoundaryEndpoint

variable {V : Scheme.{0}} [CompactSpace V]

/-- Each original fixed test has an actual vanishing power on the matching thickened stage. -/
theorem boundaryRank_test_nilpotent
    (v : V ⟶ rankPullbackThickening (Over.mk p) b n k)
    (t : invariantCoordinates ρ) (ht : t ∈ tests) :
    IsNilpotent ((v ≫ boundaryRankProductMap n o U e hU s κ k n).appTop
      (boundaryCoordinate s κ t)) := by
  rw [Scheme.isNilpotent_iff_basicOpen_eq_bot, ← Scheme.preimage_basicOpen_top,
    boundaryCoordinate_basicOpen]
  apply eq_bot_iff.mpr
  intro x hx
  exact hx ((mem_closedOrbitImage_iff_tests ρ Z (completeChart_isClosed (Fin n) o U)
    _).mp (boundaryRank_matching_complete n o U e hU s κ k (v x)) t ht)

/-- The original finite test ideal has a vanishing power after this actual restriction. -/
theorem boundaryRank_testIdeal_nilpotent
    (v : V ⟶ rankPullbackThickening (Over.mk p) b n k) :
    IsNilpotent ((boundaryTestIdeal s κ tests).map
      (v ≫ boundaryRankProductMap n o U e hU s κ k n).appTop.hom) := by
  apply ((boundaryTestIdeal_fg s κ tests).map _).isNilpotent_iff_le_nilradical.mpr
  rw [Ideal.map_le_iff_le_comap]
  change Ideal.span _ ≤ _
  rw [Ideal.span_le]
  rintro _ ⟨t, ht, rfl⟩
  exact mem_nilradical.mpr (boundaryRank_test_nilpotent n o U e hU s κ k v t ht)

end FLT.Mazur.EquivalenceRelationNormalizedFrames
