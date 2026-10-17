/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.HilbertOrbitMixedBoundaryKernel
public import FLT.Mazur.RelativeSubmoduleQuotient
public import FLT.Mazur.BoundaryCorrectionMixedNumerators

/-!
# The actual local error inside the exact mixed boundary quotient

The relative discrepancy class embeds in the entire mixed quotient. Flat
localization detects it exactly and produces one original simultaneous
boundary-kernel correction after clearing a denominator.
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

/-- The actual discrepancy in the quotient of exact mixed boundary sections by corrections. -/
def originalRelativeMixedError (t : D) : N ⧸ (K).comap (N).subtype :=
  ((K).comap (N).subtype).mkQ
    ⟨BoundaryCorrectionIdeal.mixedDiscrepancy Fp Gq (lifts f hL d V c k W hW t),
      originalLiftDiscrepancy_mem_boundary f hL d V c k W hW t⟩

/-- The relative error maps to the same full positive discrepancy class. -/
theorem originalRelativeMixedError_inclusion (t : D) :
    RelativeSubmoduleQuotient.inclusion N K
        (originalRelativeMixedError f hL d V c k W hW t) =
      (K).mkQ (BoundaryCorrectionIdeal.mixedDiscrepancy Fp Gq
        (lifts f hL d V c k W hW t)) := rfl

attribute [local irreducible] originalBoundaryExtendedCokernelAddCommGroup
  originalBoundaryExtendedCokernelModule originalBoundaryLiftErrorClass
  invariantSheaf originalClosedEquivalence originalClosedInvariantMap
  originalBoundarySource originalBoundarySourceMap
  originalClosedRelation originalClosedFst originalClosedSnd originalClosedArrow

attribute [local irreducible] originalRelativeMixedError

variable (S : Type*) [CommRing S]
  [Algebra ((invariantSheaf (equivalence f hL d V c k)).obj.obj (op W)) S]

/-- Flat scalar extension retains the exact relative obstruction without discarding equations. -/
theorem originalBoundaryError_eq_zero_iff_relative [Module.Flat Ω S] (t : D) :
    originalBoundaryLiftErrorClass f hL d V c k W hW S t = 0 ↔
      (1 ⊗ₜ[Ω] originalRelativeMixedError f hL d V c k W hW t :
        S ⊗[Ω] (N ⧸ (K).comap (N).subtype)) = 0 := by
  refine (originalBoundaryError_eq_zero_iff_mixed f hL d V c k W hW S t).trans ?_
  unfold originalRelativeMixedError
  exact (RelativeSubmoduleQuotient.tmul_eq_zero_iff N K S
    ⟨_, originalLiftDiscrepancy_mem_boundary f hL d V c k W hW t⟩).symm

variable (M : Submonoid ((invariantSheaf (equivalence f hL d V c k)).obj.obj (op W)))
  [IsLocalization M S]

/-- Local vanishing constructs an exact simultaneous correction over the original chart rings. -/
theorem originalBoundaryError_localized_iff_kernel (t : D) :
    originalBoundaryLiftErrorClass f hL d V c k W hW S t = 0 ↔
      ∃ (a : M) (z : ∀ j : Charts, Ac j),
        BoundaryCorrectionIdeal.boundaryCoordinates Hb z = 0 ∧
        BoundaryCorrectionIdeal.mixedDiscrepancy Fp Gq z =
          a.val • BoundaryCorrectionIdeal.mixedDiscrepancy Fp Gq
            (lifts f hL d V c k W hW t) := by
  rw [originalBoundaryError_eq_zero_iff_mixed f hL d V c k W hW S t]
  unfold originalBoundaryMixedCorrectionImage
  exact BoundaryCorrectionIdeal.localized_mixed_eq_zero_iff_kernel Hb Fp Gq M S _

/-- Subtracting that correction constructs compatible original numerators after one denominator. -/
theorem originalBoundaryError_localized_iff_numerator (t : D) :
    originalBoundaryLiftErrorClass f hL d V c k W hW S t = 0 ↔
      ∃ (a : M) (v : ∀ j : Charts, Ac j),
        BoundaryCorrectionIdeal.boundaryCoordinates Hb v =
          a.val • BoundaryCorrectionIdeal.boundaryCoordinates Hb
            (lifts f hL d V c k W hW t) ∧
        BoundaryCorrectionIdeal.mixedDiscrepancy Fp Gq v = 0 := by
  rw [originalBoundaryError_eq_zero_iff_mixed f hL d V c k W hW S t]
  unfold originalBoundaryMixedCorrectionImage
  exact BoundaryCorrectionIdeal.localized_mixed_eq_zero_iff_numerator Hb Fp Gq M S _

end OrbitBoundaryAtlas.FiniteAtlas
end FLT.Mazur.HilbertChart.AffineRestriction
