/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.HilbertOrbitBoundarySourceErrorCriterion
public import FLT.Mazur.FiniteErrorReducedInclusion

/-!
# Internal reduction of the actual boundary obstruction image

The reduced inclusion retains its kernel. Finite generation, injectivity of
this inclusion, and ambient residual vanishing together imply actual error
vanishing. None of these three geometric inputs is inferred from finite charts.
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
  originalBoundaryExtendedCokernelModule invariantSheaf originalClosedEquivalence
  originalClosedInvariantMap originalBoundarySource originalBoundarySourceMap
  originalClosedRelation originalClosedFst originalClosedSnd originalClosedArrow
  SchemeOpenEnvelope.denominatorIdeal

local notation "M" => originalBoundaryExtendedCokernel f hL d V c k W hW S
local notation "g" => originalBoundarySealedObstructionMap f hL d V c k W hW S
local notation "Q" => LinearMap.range g

/-- The actual reduced inclusion, with the full mixed-equation cokernel as ambient module. -/
def originalBoundaryReducedInclusion (J : Ideal S) :
    (Q ⧸ J • (⊤ : Submodule S Q)) →ₗ[S] M ⧸ J • (⊤ : Submodule S M) :=
  SubmoduleReduction.inclusion J Q

/-- Its kernel is the actual ambient intersection modulo internal multiples. -/
theorem originalBoundaryReducedInclusion_kernel (J : Ideal S) :
    LinearMap.ker (originalBoundaryReducedInclusion f hL d V c k W hW S J) =
      ((J • (⊤ : Submodule S M)).comap (Q).subtype).map
        (J • (⊤ : Submodule S Q)).mkQ :=
  SubmoduleReduction.ker_inclusion J Q

variable [IsLocalRing S]
local notation "J" => IsLocalRing.maximalIdeal S

/-- Residual vanishing of the actual scalar generators places the whole image in JM. -/
theorem originalBoundaryImage_le_residual
    (hzero : ∀ t : D, originalBoundaryLiftErrorClass f hL d V c k W hW S t ∈
      J • (⊤ : Submodule S M)) : Q ≤ J • (⊤ : Submodule S M) := by
  rw [originalBoundarySealedObstruction_range]
  apply Submodule.span_le.mpr
  rintro _ ⟨t, rfl⟩
  exact hzero t

/-- Actual error vanishing follows from finite image, injective reduction and residual vanishing. -/
theorem originalBoundaryLiftErrorClass_eq_zero_of_reduced_inclusion
    (hfg : (Q).FG)
    (hinj : Function.Injective
      (originalBoundaryReducedInclusion f hL d V c k W hW S J))
    (hzero : ∀ t : D, originalBoundaryLiftErrorClass f hL d V c k W hW S t ∈
      J • (⊤ : Submodule S M)) (t : D) :
    originalBoundaryLiftErrorClass f hL d V c k W hW S t = 0 := by
  have hQ := FiniteErrorReduction.eq_bot_of_reduced_inclusion Q hfg hinj
    (originalBoundaryImage_le_residual f hL d V c k W hW S hzero)
  have ht := originalBoundaryLiftErrorClass_mem_range f hL d V c k W hW S t
  rw [hQ, Submodule.mem_bot] at ht
  exact ht

/-- Flatness of the actual cokernel modulo the boundary image supplies reduction injectivity. -/
theorem originalBoundaryReducedInclusion_injective_of_flat [Module.Flat S (M ⧸ Q)] :
    Function.Injective (originalBoundaryReducedInclusion f hL d V c k W hW S J) :=
  SubmoduleReduction.inclusion_injective_of_flat_quotient J Q

end OrbitBoundaryAtlas.FiniteAtlas
end FLT.Mazur.HilbertChart.AffineRestriction
