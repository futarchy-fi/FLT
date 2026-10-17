/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.HilbertOrbitRelativeMixedError
public import FLT.Mazur.RelativeSubmoduleQuotientExact

/-!
# Exact projection to the actual mixed boundary quotient

All original removable corrections lie in the exact mixed boundary module.
Consequently the full correction quotient maps onto the boundary quotient,
with exactly the relative quotient as kernel. Flatness of this specified
boundary quotient suffices for arbitrary residue base change; it remains an input.
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

/-- The actual full correction quotient maps onto the unchanged mixed boundary quotient. -/
def originalMixedBoundaryProjection : (Cmix ⧸ K) →ₗ[Ω] Cmix ⧸ N :=
  RelativeSubmoduleQuotient.boundaryProjection N K
    (originalMixedCorrectionImage_le_boundary f hL d V c k W hW)

/-- Every actual mixed boundary quotient class lifts before forgetting corrections. -/
theorem originalMixedBoundaryProjection_surjective :
    Function.Surjective (originalMixedBoundaryProjection f hL d V c k W hW) :=
  RelativeSubmoduleQuotient.boundaryProjection_surjective N K
    (originalMixedCorrectionImage_le_boundary f hL d V c k W hW)

/-- The relative mixed quotient is exactly the kernel of the actual boundary projection. -/
theorem originalMixedBoundaryProjection_exact :
    Function.Exact (RelativeSubmoduleQuotient.inclusion N K)
      (originalMixedBoundaryProjection f hL d V c k W hW) :=
  RelativeSubmoduleQuotient.boundaryProjection_exact N K
    (originalMixedCorrectionImage_le_boundary f hL d V c k W hW)

attribute [local irreducible] originalBoundaryExtendedCokernelAddCommGroup
  originalBoundaryExtendedCokernelModule originalBoundaryLiftErrorClass
  invariantSheaf originalClosedEquivalence originalClosedInvariantMap
  originalBoundarySource originalBoundarySourceMap
  originalClosedRelation originalClosedFst originalClosedSnd originalClosedArrow
  originalRelativeMixedError

variable (S : Type*) [CommRing S]
  [Algebra ((invariantSheaf (equivalence f hL d V c k)).obj.obj (op W)) S]

/-- A flat actual boundary quotient preserves the relative inclusion over any scalar algebra. -/
theorem originalRelativeMixedInclusion_injective_of_boundary_flat
    [Module.Flat Ω (Cmix ⧸ N)] :
    Function.Injective ((RelativeSubmoduleQuotient.inclusion N K).lTensor S) :=
  RelativeSubmoduleQuotient.lTensor_injective_of_flat_boundary N K
    (originalMixedCorrectionImage_le_boundary f hL d V c k W hW) S

/-- Boundary-quotient flatness lets residual scalar errors detect the relative class. -/
theorem originalBoundaryError_eq_zero_iff_relative_of_boundary_flat
    [Module.Flat Ω (Cmix ⧸ N)] (t : D) :
    originalBoundaryLiftErrorClass f hL d V c k W hW S t = 0 ↔
      (1 ⊗ₜ[Ω] originalRelativeMixedError f hL d V c k W hW t :
        S ⊗[Ω] (N ⧸ (K).comap (N).subtype)) = 0 := by
  refine (originalBoundaryError_eq_zero_iff_mixed f hL d V c k W hW S t).trans ?_
  unfold originalRelativeMixedError
  exact (RelativeSubmoduleQuotient.tmul_eq_zero_iff_of_flat_boundary N K
    (originalMixedCorrectionImage_le_boundary f hL d V c k W hW) S
    ⟨_, originalLiftDiscrepancy_mem_boundary f hL d V c k W hW t⟩).symm

end OrbitBoundaryAtlas.FiniteAtlas
end FLT.Mazur.HilbertChart.AffineRestriction
