/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.HilbertOrbitRelativeMixedConnecting
public import FLT.Mazur.RelativeConnectingImageReduction

/-!
# Original representatives of the actual relative error image

Compatible original chart discrepancies form a submodule between actual
corrections and the exact mixed boundary module. They are exactly the
preimage of the original relative connecting image, before any reduction.
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
local notation "E" => (pullOpen e W).val

variable (hW : IsAffineOpen (pullOpen (equivalence f hL d V c k) W).val)
local notation "Charts" => finiteCharts f hL d V c k W hW

attribute [local irreducible] originalChartScalarMap
local notation "Ω" => (invariantSheaf e).obj.obj (op W)
local notation "Ac" => chartCoordinateRing f hL d V c k W hW
local notation "Bc" => chartBoundaryCoordinateRing f hL d V c k W hW
local notation "Cc" => mixedCoordinateRing f hL d V c k W hW

local notation "ec" => originalClosedEquivalence f hL d V c k
local notation "m" => originalClosedInvariantMap f hL d V c k
local notation "Wc" => (TopologicalSpace.Opens.map (m).base).obj W
local notation "D" => (invariantSheaf ec).obj.obj (op Wc)
local notation "ρ" => originalClosedSectionPullback f hL d V c k W

attribute [local instance] originalBoundarySectionAlgebra originalCorrectionBoundaryAlgebra
  originalCorrectionChartAlgebra originalCorrectionMixedAlgebra
attribute [local irreducible] originalBoundaryCoefficientLinearMap
  BoundaryCorrectionIdeal.originalCorrectionOperator
  originalCorrectionBoundaryHom originalCorrectionFirstHom originalCorrectionSecondHom
local notation "Hb" => originalCorrectionBoundaryHom f hL d V c k W hW
local notation "Fp" => originalCorrectionFirstHom f hL d V c k W hW
local notation "Gq" => originalCorrectionSecondHom f hL d V c k W hW
local notation "β" => originalBoundaryCoefficientLinearMap f hL d V c k W hW
local notation "i" => Over.Hom.left (originalBoundarySourceMap f hL d V c k)
local notation "ef" => fullRelationSchemeEquivalence f hL d V c k
local notation "n" => fun j : Charts ↦ j.val.size
local notation "o" => fun j : Charts ↦ j.val.label
local notation "U" => fun j : Charts ↦ j.val.domain
local notation "hU" => fun j : Charts ↦ j.val.stable
local notation "Cmix" => (∀ j l : Charts, Cc j l)

attribute [local irreducible] originalMixedBoundaryKernel originalBoundaryMixedCorrectionImage
local notation "N" => originalMixedBoundaryKernel f hL d V c k W hW
local notation "K" => originalBoundaryMixedCorrectionImage f hL d V c k W hW

/-- Mixed errors of original families whose boundary comes from an original boundary section. -/
def originalCompatibleMixedDiscrepancies : Submodule Ω Cmix :=
  RelativeBoundaryConnectingMap.compatibleDiscrepancies
    (BoundaryCorrectionIdeal.boundaryCoordinates Hb)
    (BoundaryCorrectionIdeal.mixedDiscrepancy Fp Gq) β

local notation "H" => originalCompatibleMixedDiscrepancies f hL d V c k W hW

/-- Actual boundary-zero corrections lie in the compatible mixed discrepancy module. -/
theorem originalCorrection_le_compatibleMixed : K ≤ H := by
  unfold originalBoundaryMixedCorrectionImage originalCompatibleMixedDiscrepancies
  exact RelativeBoundaryConnectingMap.correction_le_compatibleDiscrepancies _ _ _

/-- Actual compatible mixed errors satisfy the exact mixed boundary equations. -/
theorem originalCompatibleMixed_le_boundary : H ≤ N := by
  have hKN := originalMixedCorrectionImage_le_boundary f hL d V c k W hW
  unfold originalBoundaryMixedCorrectionImage at hKN
  unfold originalCompatibleMixedDiscrepancies
  exact RelativeBoundaryConnectingMap.compatibleDiscrepancies_le
    (BoundaryCorrectionIdeal.boundaryCoordinates Hb)
    (BoundaryCorrectionIdeal.mixedDiscrepancy Fp Gq) N β
    (lifts f hL d V c k W hW)
    (originalBoundaryCoefficientLinearMap_lifts f hL d V c k W hW)
    (originalLiftDiscrepancy_mem_boundary f hL d V c k W hW) hKN

/-- The actual error image, kept as one submodule for reduction and its kernel. -/
def originalRelativeMixedImage : Submodule Ω (N ⧸ (K).comap (N).subtype) :=
  LinearMap.range (originalRelativeMixedConnectingMap f hL d V c k W hW)

attribute [local irreducible] originalRelativeMixedImage
local notation "Q" => originalRelativeMixedImage f hL d V c k W hW

/-- The preimage of the actual error image consists exactly of original compatible discrepancies. -/
theorem originalRelativeMixedImage_preimage :
    (Q).comap
      ((K).comap (N).subtype).mkQ = (H).comap (N).subtype := by
  unfold originalRelativeMixedImage originalRelativeMixedConnectingMap
    originalCompatibleMixedDiscrepancies
    originalBoundaryMixedCorrectionImage
  exact RelativeBoundaryConnectingMap.connecting_range_comap _ _ _ _ _ _ _

end OrbitBoundaryAtlas.FiniteAtlas
end FLT.Mazur.HilbertChart.AffineRestriction
