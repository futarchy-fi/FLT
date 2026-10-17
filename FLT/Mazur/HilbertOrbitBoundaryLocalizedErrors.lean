/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.HilbertOrbitBoundaryScalarImage
public import FLT.Mazur.BoundaryCorrectionLocalizedVanishing
public import FLT.Mazur.FiniteLocalSpanVanishing

/-!
# Original lifts detected by localized actual scalar errors

Vanishing of the actual full scalar class is equivalent to an original
invariant lift after multiplying by one denominator. At a contracted source
prime, this denominator avoids the actual source prime.
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


attribute [local irreducible] originalBoundarySealedObstructionMap
  originalBoundaryLiftErrorClass

attribute [local irreducible] originalBoundaryExtendedCokernelAddCommGroup
  originalBoundaryExtendedCokernelModule
attribute [local irreducible] invariantSheaf originalClosedEquivalence
  originalClosedInvariantMap originalBoundarySource originalBoundarySourceMap
  originalClosedRelation originalClosedFst originalClosedSnd originalClosedArrow
  SchemeOpenEnvelope.denominatorIdeal

variable (U : Submonoid
  ((invariantSheaf (equivalence f hL d V c k)).obj.obj (op W))) [IsLocalization U S]

/-- The localized actual error vanishes precisely after an original denominator lift. -/
theorem originalBoundaryLiftErrorClass_localized_eq_zero_iff (t : D) :
    originalBoundaryLiftErrorClass f hL d V c k W hW S t = 0 ↔
      ∃ a : U, ∃ b : Ω, ρ b = a.val • t := by
  rw [← originalBoundarySealedObstruction_scalar]
  have h := BoundaryCorrectionIdeal.boundaryCokernelMap_localized_eq_zero_iff
    Hb Fp Gq 0 β U S t
  change originalBoundarySealedObstructionMap f hL d V c k W hW S (1 ⊗ₜ[Ω] t) = 0 ↔ _
  unfold originalBoundarySealedObstructionMap originalBoundaryExtendedObstructionMap
    originalBoundaryExtendedCokernel originalBoundaryExtendedCokernelAddCommGroup
    originalBoundaryExtendedCokernelModule
  refine h.trans ?_
  constructor
  · rintro ⟨a, ha⟩
    exact ⟨a, (originalBoundaryObstruction_eq_zero_iff_lift f hL d V c k W hW _).mp ha⟩
  · rintro ⟨a, ha⟩
    exact ⟨a, (originalBoundaryObstruction_eq_zero_iff_lift f hL d V c k W hW _).mpr ha⟩

/-- A finite divisible container exists exactly when an original denominator lift exists. -/
theorem originalBoundaryLiftErrorClass_local_finite_iff [IsLocalRing S] (t : D) :
    (∃ Q : Submodule S (originalBoundaryExtendedCokernel f hL d V c k W hW S),
      Q.FG ∧ Q ≤ IsLocalRing.maximalIdeal S • Q ∧
        originalBoundaryLiftErrorClass f hL d V c k W hW S t ∈ Q) ↔
      ∃ a : U, ∃ b : Ω, ρ b = a.val • t := by
  rw [FiniteErrorReduction.exists_finite_local_divisible_container_iff,
    originalBoundaryLiftErrorClass_localized_eq_zero_iff f hL d V c k W hW S U]

end OrbitBoundaryAtlas.FiniteAtlas
end FLT.Mazur.HilbertChart.AffineRestriction
