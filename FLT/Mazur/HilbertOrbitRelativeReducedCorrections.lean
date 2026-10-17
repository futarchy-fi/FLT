/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.HilbertOrbitRelativeReductionKernel
public import FLT.Mazur.RelativeBoundaryReducedCorrections

/-!
# Original simultaneous corrections of the relative residue error

Reduction of the canonical relative error is zero exactly when a single
original chart family preserves the boundary coefficients and has mixed
discrepancy in the scalar multiple of the exact mixed boundary kernel.
The ambient scalar error uses the larger ambient multiple unless the lost
reduction classes have been absorbed by actual corrections.
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

variable (J : Ideal ((invariantSheaf (equivalence f hL d V c k)).obj.obj (op W)))

/-- Relative residue vanishing constructs original lifts with exact boundary and error in JN. -/
theorem originalRelativeResidue_eq_zero_iff_lift (t : D) :
    (1 ⊗ₜ[Ω] originalRelativeMixedError f hL d V c k W hW t :
      (Ω ⧸ J) ⊗[Ω] (N ⧸ (K).comap (N).subtype)) = 0 ↔
        ∃ v : ∀ j : Charts, Ac j,
          BoundaryCorrectionIdeal.boundaryCoordinates Hb v = β t ∧
            BoundaryCorrectionIdeal.mixedDiscrepancy Fp Gq v ∈ J • N := by
  have hKN := originalMixedCorrectionImage_le_boundary f hL d V c k W hW
  unfold originalBoundaryMixedCorrectionImage at hKN ⊢
  unfold originalRelativeMixedError originalBoundaryMixedCorrectionImage
  refine (RelativeBoundaryConnectingMap.relative_residue_eq_zero_iff_lift
    (BoundaryCorrectionIdeal.boundaryCoordinates Hb)
    (BoundaryCorrectionIdeal.mixedDiscrepancy Fp Gq) J N hKN
    (lifts f hL d V c k W hW t)
    (originalLiftDiscrepancy_mem_boundary f hL d V c k W hW t)).trans ?_
  constructor
  · rintro ⟨v, hb, hd⟩
    exact ⟨v, hb.trans (originalBoundaryCoefficientLinearMap_lifts f hL d V c k W hW t), hd⟩
  · rintro ⟨v, hb, hd⟩
    exact ⟨v, hb.trans (originalBoundaryCoefficientLinearMap_lifts f hL d V c k W hW t).symm,
      hd⟩

/-- Relative residue vanishing also constructs one exact boundary-zero correction family. -/
theorem originalRelativeResidue_eq_zero_iff_kernel (t : D) :
    (1 ⊗ₜ[Ω] originalRelativeMixedError f hL d V c k W hW t :
      (Ω ⧸ J) ⊗[Ω] (N ⧸ (K).comap (N).subtype)) = 0 ↔
        ∃ z : ∀ j : Charts, Ac j,
          BoundaryCorrectionIdeal.boundaryCoordinates Hb z = 0 ∧
            BoundaryCorrectionIdeal.mixedDiscrepancy Fp Gq (lifts f hL d V c k W hW t) -
              BoundaryCorrectionIdeal.mixedDiscrepancy Fp Gq z ∈ J • N := by
  have hKN := originalMixedCorrectionImage_le_boundary f hL d V c k W hW
  unfold originalBoundaryMixedCorrectionImage at hKN ⊢
  unfold originalRelativeMixedError originalBoundaryMixedCorrectionImage
  exact RelativeBoundaryConnectingMap.relative_residue_eq_zero_iff_kernel
    (BoundaryCorrectionIdeal.boundaryCoordinates Hb)
    (BoundaryCorrectionIdeal.mixedDiscrepancy Fp Gq) J N hKN
    (lifts f hL d V c k W hW t)
    (originalLiftDiscrepancy_mem_boundary f hL d V c k W hW t)

attribute [local irreducible] originalBoundaryExtendedCokernelAddCommGroup
  originalBoundaryExtendedCokernelModule originalBoundaryLiftErrorClass
  invariantSheaf originalClosedEquivalence originalClosedInvariantMap
  originalBoundarySource originalBoundarySourceMap
  originalClosedRelation originalClosedFst originalClosedSnd originalClosedArrow
  originalRelativeMixedError

/-- Ambient residue vanishing is detected relatively once actual corrections absorb the kernel. -/
theorem originalBoundaryResidue_eq_zero_iff_relative
    (hinj : Function.Injective (originalRelativeReducedInclusion f hL d V c k W hW J))
    (t : D) :
    originalBoundaryLiftErrorClass f hL d V c k W hW (Ω ⧸ J) t = 0 ↔
      (1 ⊗ₜ[Ω] originalRelativeMixedError f hL d V c k W hW t :
        (Ω ⧸ J) ⊗[Ω] (N ⧸ (K).comap (N).subtype)) = 0 := by
  refine (originalBoundaryError_eq_zero_iff_mixed f hL d V c k W hW (Ω ⧸ J) t).trans ?_
  unfold originalRelativeMixedError
  exact (RelativeSubmoduleQuotient.relative_residue_eq_zero_iff_of_injective J N K hinj
    ⟨_, originalLiftDiscrepancy_mem_boundary f hL d V c k W hW t⟩).symm

end OrbitBoundaryAtlas.FiniteAtlas
end FLT.Mazur.HilbertChart.AffineRestriction
