/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.HilbertOrbitRelativeReductionKernel
public import FLT.Mazur.RelativeAdicAbsorption

/-!
# Nonflat adic absorption on the unchanged original mixed atlas

A finite original correction quotient gives a uniform shift for the exact
mixed boundary kernel. All-order original ambient corrections then imply
injectivity of the actual reduced inclusion. Finiteness and approximations
remain explicit inputs; neither follows from rank-stage coverage alone.
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

/-- One original adic shift works for every internal accuracy on the whole mixed atlas. -/
theorem originalMixed_exists_shifted_absorption (hΩ : IsNoetherianRing Ω)
    (hfinite : Module.Finite Ω (Cmix ⧸ K)) :
    ∃ c₀ : ℕ, ∀ n₀ : ℕ,
      N ⊓ (K ⊔ J ^ (n₀ + c₀) • (⊤ : Submodule Ω Cmix)) ≤ K ⊔ J ^ n₀ • N := by
  let _ := hΩ
  let _ := hfinite
  exact RelativeSubmoduleQuotient.exists_shifted_absorption J N K

/-- Actual approximating corrections absorb the full nonflat original reduction kernel. -/
theorem originalRelativeReducedInclusion_injective_of_adic (hΩ : IsNoetherianRing Ω)
    (hfinite : Module.Finite Ω (Cmix ⧸ K))
    (h : ∀ x ∈ N ⊓ J • (⊤ : Submodule Ω Cmix), ∀ n₀ : ℕ,
      x ∈ K ⊔ J ^ (n₀ + 1) • (⊤ : Submodule Ω Cmix)) :
    Function.Injective (originalRelativeReducedInclusion f hL d V c k W hW J) := by
  let _ := hΩ
  let _ := hfinite
  exact RelativeSubmoduleQuotient.reducedInclusion_injective_of_approximations J N K
    (originalMixedCorrectionImage_le_boundary f hL d V c k W hW) h

end OrbitBoundaryAtlas.FiniteAtlas
end FLT.Mazur.HilbertChart.AffineRestriction
