/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.HilbertOrbitSelfEmbeddingDiscrepancy
public import FLT.Mazur.HilbertOrbitResidualCorrectionAssembly

/-!
# Independent off-diagonal equations in the original correction problem

Permutation invariance proves all diagonal embedding equations automatically.
The remaining correction witnesses keep every independent off-diagonal pair,
as well as the exact original residual and boundary equations. This removes
redundant equations without assuming existence of the remaining corrections.
-/

@[expose] public noncomputable section
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry Opposite
namespace FLT.Mazur.HilbertChart.AffineRestriction
open CartierAbel SchemePicard FCurve EquivalenceRelationNormalizedFrames
open RelativeRelationOrbit InvariantOpenRelationDiagram
open FiniteGroupRestriction SchemeFiniteGroupQuotient
set_option backward.isDefEq.respectTransparency true
set_option backward.defeqAttrib.useBackward true
attribute [local irreducible] relativeFppfSheaf AmpleLineBundle
variable {R : Type} [CommRing R] [Algebra.FiniteType ℤ R] {X : Scheme}
  (f : X ⟶ Spec (.of R)) [IsProper f] [Flat f] [GeometricallyIntegral f]
  [SmoothOfRelativeDimension 1 f] {L : X.Modules} (hL : AmpleLineBundle L)
  (d : ℕ) (V : Over (Spec (.of R))) [IsAffine V.left] [Etale V.hom]
  (c : (relativeFppfSheaf f).obj.obj (op V))
  {A : Over (Spec (.of R))} [IsAffine A.left]
  (k : A ⟶ variableHilbertTest f d V) [IsOpenImmersion k.left]
attribute [local irreducible] relation fst snd equivalence
  EquivalenceRelationNormalizedFrames.source
namespace OrbitBoundaryAtlas.FiniteAtlas
attribute [local irreducible] finiteCharts lifts obstruction
  scalarFamily normalizedBoundaryChartMap normalizedOrbitBoundaryCoefficient
local notation "e" => equivalence f hL d V c k
variable (W : TopologicalSpace.Opens (Orbit (equivalence f hL d V c k)))
set_option quotPrecheck false
local notation "E" => (pullOpen e W).val

variable (hW : IsAffineOpen (pullOpen (equivalence f hL d V c k) W).val)
local notation "Charts" => finiteCharts f hL d V c k W hW

local notation "ef" => fullRelationSchemeEquivalence f hL d V c k
local notation "Ω" => (invariantSheaf e).obj.obj (op W)
local notation "Cc" => mixedCoordinateRing f hL d V c k W hW

attribute [local instance] originalCorrectionMixedAlgebra
attribute [local instance] originalMixedResidualAlgebra
local notation "Cr" => originalMixedResidualRing f hL d V c k W hW
local notation "N" => originalMixedBoundaryKernel f hL d V c k W hW
local notation "extR" => originalMixedResidualExtension f hL d V c k W hW
local notation "resR" => originalMixedResidualRestriction f hL d V c k W hW

local notation "extF" => originalResidualFamilyExtension f hL d V c k W hW
local notation "resF" => originalResidualFamilyRestriction f hL d V c k W hW

attribute [local instance] originalCorrectionChartAlgebra originalCorrectionBoundaryAlgebra
local notation "Ac" => chartCoordinateRing f hL d V c k W hW
local notation "Hb" => originalCorrectionBoundaryHom f hL d V c k W hW
local notation "Fp" => originalCorrectionFirstHom f hL d V c k W hW
local notation "Gq" => originalCorrectionSecondHom f hL d V c k W hW
local notation "K" => originalBoundaryMixedCorrectionImage f hL d V c k W hW
local notation "δ" => BoundaryCorrectionIdeal.mixedDiscrepancy Fp Gq

attribute [local irreducible] BoundaryCorrectionIdeal.mixedDiscrepancy
  BoundaryCorrectionIdeal.boundaryCoordinates originalCorrectionBoundaryHom
  originalCorrectionFirstHom originalCorrectionSecondHom
  originalResidualFamilyExtension originalResidualFamilyRestriction
local notation "Kr" => originalResidualCorrectionModule f hL d V c k W hW
local notation "bdy" => BoundaryCorrectionIdeal.boundaryCoordinates Hb

/-- Exact residual correction membership only needs the independent off-diagonal equations. -/
theorem mem_originalResidualCorrection_iff_offDiagonal (a : ∀ j l : Charts, Cr j l) :
    a ∈ Kr ↔ ∃ u : ∀ j : Charts, Ac j, bdy u = 0 ∧ resF (δ u) = a ∧
      ∀ (j l : Charts), j ≠ l → ∀ ι : Fin l.val.size ↪ Fin j.val.size,
        originalMixedEmbeddingCoefficient f hL d V c k W hW j l ι (δ u j l) = 0 := by
  refine (mem_originalResidualCorrection_iff f hL d V c k W hW a).trans ?_
  constructor
  · rintro ⟨u, hu, hr, hg⟩
    exact ⟨u, hu, hr, fun j l _ ↦ hg j l⟩
  · rintro ⟨u, hu, hr, hg⟩
    refine ⟨u, hu, hr, fun j l ι ↦ ?_⟩
    by_cases h : j = l
    · subst l
      exact originalMixedDiscrepancy_selfEmbedding f hL d V c k W hW u j ι
    · exact hg j l h ι

/-- For an actual lift discrepancy, the embedding stage only requires off-diagonal equations. -/
theorem originalDiscrepancy_mem_iff_offDiagonal_stages (v : ∀ j : Charts, Ac j) :
    δ v ∈ K ↔ ∃ u : ∀ j : Charts, Ac j, bdy u = 0 ∧
      (∀ (j l : Charts), j ≠ l → ∀ ι : Fin l.val.size ↪ Fin j.val.size,
        originalMixedEmbeddingCoefficient f hL d V c k W hW j l ι ((δ v - δ u) j l) = 0) ∧
      resF (δ v - δ u) ∈ Kr := by
  refine (originalMixedCorrection_mem_iff_residual_stages f hL d V c k W hW (δ v)).trans ?_
  constructor
  · rintro ⟨u, hu, hg, hr⟩
    exact ⟨u, hu, fun j l _ ↦ hg j l, hr⟩
  · rintro ⟨u, hu, hg, hr⟩
    refine ⟨u, hu, fun j l ι ↦ ?_, hr⟩
    by_cases h : j = l
    · subst l
      exact originalMixedDiscrepancy_sub_selfEmbedding f hL d V c k W hW v u j ι
    · exact hg j l h ι

end OrbitBoundaryAtlas.FiniteAtlas
end FLT.Mazur.HilbertChart.AffineRestriction
