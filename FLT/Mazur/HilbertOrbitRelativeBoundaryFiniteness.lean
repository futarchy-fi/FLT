/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.HilbertOrbitRelativeResidueUnit
public import FLT.Mazur.ScalarRestrictionFiniteness

/-!
# Local boundary source finiteness and the actual relative image

The kernel of the actual relative connecting map is the cyclic scalar
restriction image. Thus local relative image finiteness is equivalent to
finiteness of the localized boundary source. In that finite case, generation
of the source residue by the unit detects exact scalar error vanishing.
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
local notation "o" => fun j : Charts ↦ j.val.label
local notation "U" => fun j : Charts ↦ j.val.domain
local notation "hU" => fun j : Charts ↦ j.val.stable
local notation "Cmix" => (∀ j l : Charts, Cc j l)

attribute [local irreducible] originalMixedBoundaryKernel originalBoundaryMixedCorrectionImage
local notation "N" => originalMixedBoundaryKernel f hL d V c k W hW
local notation "K" => originalBoundaryMixedCorrectionImage f hL d V c k W hW

attribute [local irreducible] originalRelativeMixedConnectingMap
  originalRelativeMixedError originalBoundaryLiftErrorClass
  originalBoundaryExtendedCokernelAddCommGroup originalBoundaryExtendedCokernelModule
  invariantSheaf originalClosedEquivalence originalClosedInvariantMap
  originalBoundarySource originalBoundarySourceMap originalClosedRelation
  originalClosedFst originalClosedSnd originalClosedArrow
local notation "g" => originalRelativeMixedConnectingMap f hL d V c k W hW

variable (S : Type*) [CommRing S]
  [Algebra ((invariantSheaf (equivalence f hL d V c k)).obj.obj (op W)) S]
  [Module.Flat ((invariantSheaf (equivalence f hL d V c k)).obj.obj (op W)) S]

attribute [local irreducible] originalBoundaryPullbackLinearMap
local notation "r" => originalBoundaryPullbackLinearMap f hL d V c k W

attribute [local irreducible] SourceImageNakayama.residueRestriction
  IsLocalRing.maximalIdeal

/-- Local relative image finiteness is exactly local boundary source finiteness. -/
theorem originalRelativeScalarImage_fg_iff_boundary_finite :
    (LinearMap.range ((g).baseChange S)).FG ↔ Module.Finite S (S ⊗[Ω] D) :=
  ScalarRestrictionImage.range_fg_iff_source_finite r g
    (originalRelativeMixedConnectingMap_ker f hL d V c k W hW) S

/-- A finite local boundary source reduces exact error vanishing to unit residue generation. -/
theorem originalBoundaryErrors_eq_zero_iff_residue_unit_of_finite [IsLocalRing S]
    [Module.Finite S (S ⊗[Ω] D)] :
    (∀ t : D, originalBoundaryLiftErrorClass f hL d V c k W hW S t = 0) ↔
      Submodule.span S {(1 ⊗ₜ[Ω] (1 : D) : S ⊗[Ω] D)} ⊔
        IsLocalRing.maximalIdeal S • (⊤ : Submodule S (S ⊗[Ω] D)) = ⊤ :=
  originalBoundaryErrors_eq_zero_iff_residue_unit f hL d V c k W hW S
    ((originalRelativeScalarImage_fg_iff_boundary_finite f hL d V c k W hW S).mpr
      inferInstance)

end OrbitBoundaryAtlas.FiniteAtlas
end FLT.Mazur.HilbertChart.AffineRestriction
