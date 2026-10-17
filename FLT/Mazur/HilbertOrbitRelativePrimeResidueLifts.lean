/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.HilbertOrbitRelativePrimeFiniteLifts
public import FLT.Mazur.HilbertOrbitRelativeResidueGenerators

/-!
# Original source-prime lift tests from residue source frames

A residue frame and finite local relative image construct a full local frame.
Exact original lifts of this finite family then test all actual scalar errors.
The source residue surjectivity route is available over arbitrary local scalars.
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

attribute [local irreducible] originalBoundaryPullbackLinearMap
  sourceSheaf invariantInclusion
local notation "r" => originalBoundaryPullbackLinearMap f hL d V c k W
local notation "T" => (sourceSheaf ec).obj.obj (op Wc)
local notation "κ" => ((invariantInclusion ec).hom.app (op Wc)).hom.comp ρ
variable (P : Ideal ((sourceSheaf (originalClosedEquivalence f hL d V c k)).obj.obj
  (op ((TopologicalSpace.Opens.map (originalClosedInvariantMap f hL d V c k).base).obj W))))
  [P.IsPrime]
local notation "S" => Localization.AtPrime (P.comap κ)

attribute [local irreducible] SourceImageNakayama.residueRestriction
  IsLocalRing.maximalIdeal

/-- Residue generators suffice for the original finite lift test at a source prime. -/
theorem originalBoundaryPrimeErrors_eq_zero_iff_residue_frame_lifts
    {n : ℕ} (t : Fin n → D) (hfg : (LinearMap.range ((g).baseChange S)).FG)
    (hres : Submodule.span S (Set.range (fun j ↦ (1 ⊗ₜ[Ω] t j : S ⊗[Ω] D))) ⊔
      LinearMap.range ((r).baseChange S) ⊔
        IsLocalRing.maximalIdeal S • (⊤ : Submodule S (S ⊗[Ω] D)) = ⊤) :
    (∀ x : D, originalBoundaryLiftErrorClass f hL d V c k W hW S x = 0) ↔
      ∃ a : Ω, κ a ∉ P ∧ ∃ v : Fin n → Ω, ∀ j, r (v j) = a • t j :=
  originalBoundaryPrimeErrors_eq_zero_iff_finite_lifts f hL d V c k W hW P t
    (originalRelativeSource_span_of_residue f hL d V c k W hW S t hfg hres)

end OrbitBoundaryAtlas.FiniteAtlas
end FLT.Mazur.HilbertChart.AffineRestriction
