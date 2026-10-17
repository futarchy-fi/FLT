/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.HilbertOrbitRelativeMixedConnecting
public import FLT.Mazur.RelativeBoundaryReductionAbsorption

/-!
# The reduction kernel of the actual relative mixed obstruction

The original correction module absorbs precisely the lost boundary residue
classes needed for injectivity. This is an exact criterion on the original
mixed coordinates, with no flatness assertion about the boundary quotient.
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

attribute [local irreducible] invariantSheaf originalClosedEquivalence originalClosedInvariantMap
  originalBoundarySource originalBoundarySourceMap originalClosedRelation originalClosedFst
  originalClosedSnd originalClosedArrow BoundaryCorrectionIdeal.mixedDiscrepancy
  BoundaryCorrectionIdeal.boundaryCoordinates

variable (J : Ideal ((invariantSheaf (equivalence f hL d V c k)).obj.obj (op W)))

/-- The residue presentation comparison for the actual relative mixed obstruction. -/
def originalRelativeReducedInclusion :
    (N ⧸ ((K).comap (N).subtype ⊔ J • (⊤ : Submodule Ω N))) →ₗ[Ω]
      Cmix ⧸ (K ⊔ J • (⊤ : Submodule Ω Cmix)) :=
  RelativeSubmoduleQuotient.reducedInclusion J N K

/-- The actual comparison retains all ambient reduction classes before taking their quotient. -/
theorem originalRelativeReducedInclusion_ker :
    LinearMap.ker (originalRelativeReducedInclusion f hL d V c k W hW J) =
      ((K ⊔ J • (⊤ : Submodule Ω Cmix)).comap (N).subtype).map
        ((K).comap (N).subtype ⊔ J • (⊤ : Submodule Ω N)).mkQ :=
  RelativeSubmoduleQuotient.ker_reducedInclusion J N K

/-- Injectivity asks only that actual corrections absorb the lost mixed boundary classes. -/
theorem originalRelativeReducedInclusion_injective_iff :
    Function.Injective (originalRelativeReducedInclusion f hL d V c k W hW J) ↔
      N ⊓ J • (⊤ : Submodule Ω Cmix) ≤ K ⊔ J • N :=
  RelativeSubmoduleQuotient.reducedInclusion_injective_iff_absorption J N K
    (originalMixedCorrectionImage_le_boundary f hL d V c k W hW)

/-- Every lost mixed boundary class must have one exact original boundary-zero correction. -/
theorem originalRelativeReducedInclusion_injective_iff_corrections :
    Function.Injective (originalRelativeReducedInclusion f hL d V c k W hW J) ↔
      ∀ x ∈ N ⊓ J • (⊤ : Submodule Ω Cmix), ∃ z : ∀ j : Charts, Ac j,
        BoundaryCorrectionIdeal.boundaryCoordinates Hb z = 0 ∧
          x - BoundaryCorrectionIdeal.mixedDiscrepancy Fp Gq z ∈ J • N := by
  have hKN := originalMixedCorrectionImage_le_boundary f hL d V c k W hW
  unfold originalBoundaryMixedCorrectionImage at hKN
  unfold originalRelativeReducedInclusion originalBoundaryMixedCorrectionImage
  exact RelativeBoundaryConnectingMap.reducedInclusion_injective_iff_boundary_corrections
    (BoundaryCorrectionIdeal.boundaryCoordinates Hb)
    (BoundaryCorrectionIdeal.mixedDiscrepancy Fp Gq) J N hKN

end OrbitBoundaryAtlas.FiniteAtlas
end FLT.Mazur.HilbertChart.AffineRestriction
