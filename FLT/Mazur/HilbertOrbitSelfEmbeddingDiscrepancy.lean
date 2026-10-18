/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.HilbertOrbitResidualCorrectionCoordinates
public import FLT.Mazur.EquivalenceRelationSelfEmbeddingAction

/-!
# Self-embedding equations vanish on the original Hilbert atlas

Every chart coefficient is already invariant under its finite permutation
action. Thus every actual discrepancy is residual-supported on each diagonal
pair, without a completeness assumption. Independent off-diagonal equations
are retained and are not identified with self equations.
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

/-- Every actual chart family solves its self-embedding equations before any correction. -/
theorem originalMixedDiscrepancy_selfEmbedding (u : ∀ j : Charts, Ac j)
    (j : Charts) (ι : Fin j.val.size ↪ Fin j.val.size) :
    originalMixedEmbeddingCoefficient f hL d V c k W hW j j ι (δ u j j) = 0 := by
  change (MixedFrames.mixedEmbeddingTestOpen ef j.val.label j.val.label
    (MixedFrames.mixedChartOpen j.val.label j.val.label j.val.domain j.val.domain).ι
    ι).ι.appTop
      ((MixedFrames.mixedChartFirst j.val.label j.val.label j.val.domain j.val.domain).appTop
        (u j).val -
       (MixedFrames.mixedChartSecond j.val.label j.val.label j.val.domain j.val.domain).appTop
        (u j).val) = 0
  rw [map_sub, sub_eq_zero]
  exact MixedFrames.mixedSelfEmbedding_branch_equalizes ef (Fin j.val.size) j.val.label
    j.val.domain j.val.stable ι (u j)

/-- The actual diagonal discrepancy is reconstructed by its exact residual coefficient. -/
theorem originalMixedDiscrepancy_selfResidual (u : ∀ j : Charts, Ac j) (j : Charts) :
    δ u j j = extR j j (resR j j (δ u j j)) :=
  (originalMixedResidual_equation_iff f hL d V c k W hW j j _ _).mpr
    ⟨rfl, originalMixedDiscrepancy_selfEmbedding f hL d V c k W hW u j⟩

/-- The residual of a corrected family still has zero on every diagonal embedding branch. -/
theorem originalMixedDiscrepancy_sub_selfEmbedding (u v : ∀ j : Charts, Ac j)
    (j : Charts) (ι : Fin j.val.size ↪ Fin j.val.size) :
    originalMixedEmbeddingCoefficient f hL d V c k W hW j j ι ((δ u - δ v) j j) = 0 := by
  change originalMixedEmbeddingCoefficient f hL d V c k W hW j j ι
    (δ u j j - δ v j j) = 0
  rw [map_sub, originalMixedDiscrepancy_selfEmbedding, originalMixedDiscrepancy_selfEmbedding,
    sub_self]

end OrbitBoundaryAtlas.FiniteAtlas
end FLT.Mazur.HilbertChart.AffineRestriction
