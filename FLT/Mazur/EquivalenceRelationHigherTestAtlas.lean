/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.EquivalenceRelationHigherScalarValuations
public import FLT.Mazur.AffineBoundaryPrincipalTestCharts

/-!
# A finite affine atlas for the entire original higher-rank open

The original finite completeness tests cover exactly the higher-rank open by
full principal affine schemes. This proves quasi-compactness of that open even
when the scalar product and scalar ring have no Noetherian hypothesis.
-/

@[expose] public noncomputable section
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
namespace FLT.Mazur.EquivalenceRelationNormalizedFrames
open RelativeOrderedTuples AffineScalarBoundaryNilpotence
open FiniteGroupRestriction SchemeFiniteGroupQuotient
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
attribute [local irreducible] source action restrictedAction boundaryProduct
variable {D A : Scheme.{0}} {p q : D ⟶ A} [IsSeparated p] [Etale p] [QuasiCompact p]
  (n : ℕ) (o : Fin n) (U : (source p q (Fin n) o).Opens)
  (e : CategoryTheory.EquivalenceRelation p q)
  (hU : ∀ g : Equiv.Perm (Fin n), (action e (Fin n) o g).hom ⁻¹ᵁ U = U)
  [IsAffine U.toScheme]
  {R T : Type} [CommRing R] [CommRing T]
  (s : R →+* invariantCoordinates (restrictedAction (action e (Fin n) o) U hU))
  (κ : R →+* T)
local notation "π" => chartBoundaryProduct n o U e hU s κ
local notation "b" => chartBoundaryEndpoint n o U e hU s κ
local notation "ρ" => restrictedAction (action e (Fin n) o) U hU
local instance higherTestAtlasOver_etale : Etale (Over.mk p).hom := ‹Etale p›
local instance higherTestAtlasOver_separated : IsSeparated (Over.mk p).hom := ‹IsSeparated p›
local instance higherTestAtlasOver_compact : QuasiCompact (Over.mk p).hom := ‹QuasiCompact p›

variable [TopologicalSpace.NoetherianSpace U.toScheme]
local notation "tests" => completeAffineOrbitTests e (Fin n) o U hU
local notation "I" => boundaryTestIdeal s κ tests
local notation "Z" => U.ι ⁻¹' completePointLocus («p» := p) («q» := q) (Fin n) o
set_option quotPrecheck false
local notation "C" => Γ(boundaryProduct s κ, ⊤)
local notation "rankOf" => boundaryPointRank n o U e hU s κ

local notation "higher" => boundaryRankOpen n o U e hU s κ (n + 1)
local notation "chart" t:max => boundaryTestChart s κ t

/-- A nonvanishing original completeness test forces genuinely higher rank. -/
theorem boundaryTestChart_le_higher (t : tests) : chart t.val ≤ higher := by
  intro z hz
  apply (mem_boundaryRankOpen_iff n o U e hU s κ z (n + 1)).mpr
  have hge := boundaryExactRank_ge n o U e hU s κ _ z
    (boundaryPointRank_spec n o U e hU s κ z)
  have hne : rankOf z ≠ n := by
    intro he
    have hI := (boundaryTestIdeal_le_iff_matching_rank n o U e hU s κ z).mpr he
    have ht := (boundaryTestIdeal_le_point_iff s κ tests z).mp hI t.val t.property
    exact (mem_boundaryTestChart s κ t.val z).mp hz ht
  omega

/-- Every higher-rank point lies in one of the finitely many original principal test charts. -/
theorem boundary_higher_mem_testChart (z : boundaryProduct s κ) (hz : z ∈ higher) :
    ∃ t : tests, z ∈ chart t.val := by
  have hr := (mem_boundaryRankOpen_iff n o U e hU s κ z (n + 1)).mp hz
  have hn : ¬ ∀ t ∈ tests, t ∈ (boundaryProjection s κ z).asIdeal := by
    intro h
    have he := (boundaryTestIdeal_le_iff_matching_rank n o U e hU s κ z).mp
      ((boundaryTestIdeal_le_point_iff s κ tests z).mpr h)
    omega
  push Not at hn
  obtain ⟨t, ht, hn⟩ := hn
  exact ⟨⟨t, ht⟩, (mem_boundaryTestChart s κ t z).mpr hn⟩

/-- The entire higher locus is the finite union of full original test charts. -/
theorem boundary_higher_eq_testChart_iSup : higher = ⨆ t : tests, chart t.val := by
  apply le_antisymm
  · intro z hz
    obtain ⟨t, ht⟩ := boundary_higher_mem_testChart n o U e hU s κ z hz
    exact TopologicalSpace.Opens.mem_iSup.mpr ⟨t, ht⟩
  · exact iSup_le (boundaryTestChart_le_higher n o U e hU s κ)

/-- The constructed finite affine atlas retains the whole higher-rank scheme structure. -/
def boundaryHigherTestCover : (higher).toScheme.OpenCover where
  I₀ := tests
  X t := (chart t.val).toScheme
  f t := (boundaryProduct s κ).homOfLE (boundaryTestChart_le_higher n o U e hU s κ t)
  mem₀ := by
    rw [Scheme.presieve₀_mem_precoverage_iff]
    refine ⟨?_, inferInstance⟩
    intro z
    obtain ⟨t, ht⟩ := boundary_higher_mem_testChart n o U e hU s κ z.val z.property
    refine ⟨t, ⟨z.val, ht⟩, ?_⟩
    apply Subtype.ext
    exact congrArg (fun f ↦ f ⟨z.val, ht⟩)
      ((boundaryProduct s κ).homOfLE_ι (boundaryTestChart_le_higher n o U e hU s κ t))

instance boundaryHigherTestCover_finite : Finite (boundaryHigherTestCover n o U e hU s κ).I₀ :=
  inferInstanceAs (Finite tests)

instance boundaryHigherTestCover_affine (t : (boundaryHigherTestCover n o U e hU s κ).I₀) :
    IsAffine ((boundaryHigherTestCover n o U e hU s κ).X t) :=
  inferInstanceAs (IsAffine (chart t.val).toScheme)

/-- A finite principal atlas proves compactness without a Noetherian scalar-product assumption. -/
theorem boundaryHigher_compactSpace : CompactSpace (higher).toScheme :=
  (boundaryHigherTestCover n o U e hU s κ).compactSpace

end FLT.Mazur.EquivalenceRelationNormalizedFrames
