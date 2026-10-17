/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.HilbertOrbitBoundaryLinearSystem
public import FLT.Mazur.BoundaryCorrectionCompatibleErrors

/-!
# Actual compatible error spaces on the original Hilbert boundary atlas

The original mixed boundary ideals and the chosen lift restrictions construct
an explicit error subspace. It contains the full correction image and the
scalar-one error without any extra geometric hypothesis. Finiteness modulo
corrections and residual divisibility are separate, still unproved obligations.
-/

@[expose] public noncomputable section
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry Opposite TensorProduct
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

variable (hW : IsAffineOpen (pullOpen (equivalence f hL d V c k) W).val)
local notation "Charts" => finiteCharts f hL d V c k W hW

attribute [local irreducible] originalChartScalarMap
local notation "Ω" => (invariantSheaf e).obj.obj (op W)
local notation "Ac" => chartCoordinateRing f hL d V c k W hW
local notation "Bc" => chartBoundaryCoordinateRing f hL d V c k W hW
local notation "Cc" => mixedCoordinateRing f hL d V c k W hW

attribute [local instance] originalCorrectionChartAlgebra originalCorrectionBoundaryAlgebra
  originalCorrectionMixedAlgebra
local notation "Hb" => originalCorrectionBoundaryHom f hL d V c k W hW
local notation "Fp" => originalCorrectionFirstHom f hL d V c k W hW
local notation "Gq" => originalCorrectionSecondHom f hL d V c k W hW
variable (t : (invariantSheaf (originalClosedEquivalence f hL d V c k)).obj.obj
  (op ((TopologicalSpace.Opens.map (originalClosedInvariantMap f hL d V c k).base).obj W)))
local notation "u" => lifts f hL d V c k W hW t
attribute [local irreducible] BoundaryCorrectionIdeal.correctionSystem
  BoundaryCorrectionIdeal.originalCorrectionOperator
  BoundaryCorrectionIdeal.compatibleErrorSubspace

/-- The exact original boundary ideal in every full independent mixed coefficient ring. -/
def originalMixedBoundaryIdeal (j l : Charts) : Ideal (Cc j l) :=
  RingHom.ker (MixedFrames.mixedChartBoundaryInclusion j.val.label l.val.label
    j.val.domain l.val.domain (originalBoundarySourceMap f hL d V c k).left).appTop.hom

attribute [local irreducible] originalMixedBoundaryIdeal
local notation "J" => originalMixedBoundaryIdeal f hL d V c k W hW

/-- The actual chosen discrepancies belong to those exact ideals. -/
theorem originalMixedDiscrepancy_mem (j l : Charts) :
    Fp j l (u j) - Gq j l (u l) ∈ J j l := by
  unfold originalMixedBoundaryIdeal
  exact lifts_difference f hL d V c k W hW t j l

/-- An actual compatible subspace of the full original equation target. -/
def originalCompatibleErrorSubspace :
    Submodule Ω ((∀ j : Charts, Bc j) × ∀ j l : Charts, Cc j l) :=
  BoundaryCorrectionIdeal.compatibleErrorSubspace Hb Fp Gq u J

attribute [local irreducible] originalCompatibleErrorSubspace

/-- The entire original correction image lies in the constructed subspace. -/
theorem originalCorrection_range_le_compatible :
    LinearMap.range (BoundaryCorrectionIdeal.originalCorrectionOperator Hb Fp Gq u) ≤
      originalCompatibleErrorSubspace f hL d V c k W hW t := by
  unfold originalCompatibleErrorSubspace
  exact BoundaryCorrectionIdeal.correction_range_le_compatible Hb Fp Gq u J

/-- The full original scalar-one error belongs to the constructed geometric subspace. -/
theorem originalScalarError_mem_compatible :
    originalCorrectionSystem f hL d V c k W hW t (1, 0) ∈
      originalCompatibleErrorSubspace f hL d V c k W hW t := by
  change BoundaryCorrectionIdeal.correctionSystem Hb Fp Gq u (1, 0) ∈ _
  unfold originalCompatibleErrorSubspace
  exact BoundaryCorrectionIdeal.scalarError_mem_compatible Hb Fp Gq u J
    (originalMixedDiscrepancy_mem f hL d V c k W hW t)

end OrbitBoundaryAtlas.FiniteAtlas
end FLT.Mazur.HilbertChart.AffineRestriction
