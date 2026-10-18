/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.EquivalenceRelationBoundaryRankEquations

/-!
# Higher boundary ranks have a unit completeness-test ideal

On a higher rank stage the original n-frame is incomplete at every point.
Consequently the original fixed tests generate the unit ideal on every affine
coefficient chart. These stages cannot be discarded when asking for nilpotence
on the full product; the matching-rank equations alone do not prove descent.
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
local instance rankSeparationOver_etale : Etale (Over.mk p).hom := ‹Etale p›
local instance rankSeparationOver_separated : IsSeparated (Over.mk p).hom := ‹IsSeparated p›
local instance rankSeparationOver_compact : QuasiCompact (Over.mk p).hom := ‹QuasiCompact p›
local notation "ρ" => restrictedAction (action e (Fin n) o) U hU
local notation "b" => chartBoundaryEndpoint n o U e hU s κ
local notation "Z" => U.ι ⁻¹' completePointLocus («p» := p) («q» := q) (Fin n) o
local notation "tests" => completeAffineOrbitTests e (Fin n) o U hU
variable (k : ℕ)


omit [TopologicalSpace.NoetherianSpace U.toScheme] in
/-- Higher rank stages have no point in the original complete orbit image. -/
theorem boundaryRank_higher_not_complete (m : ℕ) (hm : n < m)
    (y : rankPullbackThickening (Over.mk p) b m k) :
    boundaryProjection s κ (boundaryRankProductMap n o U e hU s κ k m y) ∉
      completeAffineOrbitImage e (Fin n) o U hU := by
  intro hz
  let x := rankPullbackMap (Over.mk p) b m k y
  have he : quotientMap ρ (chartBoundaryChart n o U e hU s κ x) =
      boundaryProjection s κ (chartBoundaryProduct n o U e hU s κ x) :=
    congrArg (fun f ↦ f x) (pullback.condition
      (f := quotientMap ρ) (g := boundaryProjection s κ))
  have hc : chartBoundaryChart n o U e hU s κ x ∈ Z := by
    rw [← completeAffineOrbitImage_preimage e (Fin n) o U hU]
    change quotientMap ρ (chartBoundaryChart n o U e hU s κ x) ∈
      completeAffineOrbitImage e (Fin n) o U hU
    rw [he]
    exact hz
  have hn := (chart_complete_iff_exactRank n o U _).mp hc
  have hr := rankPullback_endpoint (Over.mk p) b m k y
  exact hn.2 (rankImageOpen_antitone (Over.mk p) hm hr.1)

/-- An actual fixed test is nonzero at each higher-rank original boundary point. -/
theorem boundaryRank_higher_test (m : ℕ) (hm : n < m)
    (y : rankPullbackThickening (Over.mk p) b m k) :
    ∃ t ∈ tests, t ∉
      (boundaryProjection s κ (boundaryRankProductMap n o U e hU s κ k m y)).asIdeal := by
  have h := boundaryRank_higher_not_complete n o U e hU s κ k m hm y
  change ¬ _ ∈ closedOrbitImage ρ Z (completeChart_isClosed (Fin n) o U) at h
  rw [mem_closedOrbitImage_iff_tests] at h
  push Not at h
  exact h

attribute [local irreducible] boundaryRankProductMap chartBoundary
  chartBoundaryChart chartBoundaryProduct chartBoundaryEndpoint

/-- The original finite test ideal is the unit ideal on every affine higher-rank chart. -/
theorem boundaryRank_higher_testIdeal_top (m : ℕ) (hm : n < m)
    {V : Scheme.{0}} [IsAffine V]
    (v : V ⟶ rankPullbackThickening (Over.mk p) b m k) :
    (boundaryTestIdeal s κ tests).map
      (v ≫ boundaryRankProductMap n o U e hU s κ k m).appTop.hom = ⊤ := by
  let a := v ≫ boundaryRankProductMap n o U e hU s κ k m
  by_contra h
  obtain ⟨M, hM, hle⟩ := Ideal.exists_le_maximal
    ((boundaryTestIdeal s κ tests).map a.appTop.hom) h
  let P : PrimeSpectrum Γ(V, ⊤) := ⟨M, hM.isPrime⟩
  let x : V := V.isoSpec.inv P
  obtain ⟨t, ht, hnon⟩ := boundaryRank_higher_test n o U e hU s κ k m hm (v x)
  have hb : x ∈ V.basicOpen (a.appTop (boundaryCoordinate s κ t)) := by
    rw [← Scheme.preimage_basicOpen_top, boundaryCoordinate_basicOpen]
    exact hnon
  have he : V.toSpecΓ x = P :=
    congrArg (fun f ↦ f P) V.isoSpec.inv_hom_id
  have hnot : a.appTop (boundaryCoordinate s κ t) ∉ M := by
    change P ∈ PrimeSpectrum.basicOpen _
    rw [← he]
    change x ∈ V.toSpecΓ ⁻¹ᵁ PrimeSpectrum.basicOpen _
    rwa [Scheme.toSpecΓ_preimage_basicOpen]
  exact hnot (hle (Ideal.mem_map_of_mem _ (boundaryCoordinate_mem_testIdeal s κ tests ht)))

end FLT.Mazur.EquivalenceRelationNormalizedFrames
