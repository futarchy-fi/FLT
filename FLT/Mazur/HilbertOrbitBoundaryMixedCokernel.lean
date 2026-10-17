/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.HilbertOrbitBoundaryReducedImage
public import FLT.Mazur.BoundaryCorrectionMixedBaseChange
public import FLT.Mazur.HilbertNormalizedBoundarySurjectivity

/-!
# Actual mixed-discrepancy presentation of original boundary errors

Freeness on each actual affine chart proves boundary-block surjectivity.
Elimination then identifies the full actual extended cokernel with the tensor
of the mixed quotient. No mixed compatibility or residual vanishing is assumed.
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
variable (S : Type*) [CommRing S]
  [Algebra ((invariantSheaf (equivalence f hL d V c k)).obj.obj (op W)) S]
attribute [local irreducible] BoundaryCorrectionIdeal.ambientCorrectionOperator
  BoundaryCorrectionIdeal.ambientScalarError
local notation "F₀" => BoundaryCorrectionIdeal.ambientCorrectionOperator Hb Fp Gq 0 S
local notation "π" => (LinearMap.range F₀).mkQ


attribute [local irreducible] originalBoundaryExtendedCokernelAddCommGroup
  originalBoundaryExtendedCokernelModule originalBoundaryLiftErrorClass
  invariantSheaf originalClosedEquivalence originalClosedInvariantMap
  originalBoundarySource originalBoundarySourceMap
  originalClosedRelation originalClosedFst originalClosedSnd originalClosedArrow

set_option backward.isDefEq.respectTransparency false in
/-- Freeness of the actual normalized charts supplies all boundary-coordinate lifts. -/
theorem originalCorrectionBoundaryHom_surjective (j : Charts) : Function.Surjective (Hb j) := by
  unfold originalCorrectionBoundaryHom
  change Function.Surjective
    (normalizedBoundaryChartMap f hL d V c k j.val.size j.val.label j.val.domain j.val.stable)
  exact normalizedBoundaryChartMap_surjective f hL d V c k j.val.size j.val.label
    j.val.domain j.val.stable j.val.affine

/-- Mixed discrepancies of actual families whose boundary coordinates are exactly zero. -/
def originalBoundaryMixedCorrectionImage : Submodule Ω (∀ j l : Charts, Cc j l) :=
  BoundaryCorrectionIdeal.mixedCorrectionImage Hb Fp Gq

attribute [local irreducible] originalBoundaryMixedCorrectionImage
local notation "K" => originalBoundaryMixedCorrectionImage f hL d V c k W hW
local notation "Cmix" => (∀ j l : Charts, Cc j l)
local notation "M" => originalBoundaryExtendedCokernel f hL d V c k W hW S

/-- Exact actual vanishing is equivalent to vanishing of its positive mixed-discrepancy tensor. -/
theorem originalBoundaryError_eq_zero_iff_mixed (t : D) :
    originalBoundaryLiftErrorClass f hL d V c k W hW S t = 0 ↔
      (1 ⊗ₜ[Ω] (K).mkQ
        (BoundaryCorrectionIdeal.mixedDiscrepancy Fp Gq (lifts f hL d V c k W hW t)) :
          S ⊗[Ω] (Cmix ⧸ K)) = 0 := by
  unfold originalBoundaryLiftErrorClass originalBoundaryExtendedCokernel
    originalBoundaryExtendedCokernelAddCommGroup
    originalBoundaryMixedCorrectionImage
  exact BoundaryCorrectionIdeal.ambientScalarError_eq_zero_iff_mixed Hb Fp Gq
    (originalCorrectionBoundaryHom_surjective f hL d V c k W hW) S _

end OrbitBoundaryAtlas.FiniteAtlas
end FLT.Mazur.HilbertChart.AffineRestriction
