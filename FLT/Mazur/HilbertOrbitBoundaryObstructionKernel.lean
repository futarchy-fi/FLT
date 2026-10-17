/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.HilbertOrbitBoundaryCoefficientHom
public import FLT.Mazur.BoundaryCorrectionBoundaryKernel

/-!
# Exact kernel of the original geometric boundary obstruction

The full correction cokernel receives a linear map from actual boundary
sections. Its kernel consists exactly of restrictions of original invariant
sections. This identifies its image as an explicit quotient, without claiming
that the boundary section module or the quotient is finitely generated.
-/

@[expose] public noncomputable section
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry Opposite
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
local notation "F₀" => BoundaryCorrectionIdeal.originalCorrectionOperator Hb Fp Gq 0

/-- The full original boundary obstruction is a linear map on actual boundary sections. -/
def originalBoundaryObstructionMap :
    D →ₗ[Ω] (((∀ j : Charts, Bc j) × ∀ j l : Charts, Cc j l) ⧸ LinearMap.range F₀) :=
  BoundaryCorrectionIdeal.originalBoundaryCokernelMap Hb Fp Gq 0 β

attribute [local irreducible] originalBoundaryObstructionMap

set_option backward.isDefEq.respectTransparency false in
/-- Its vanishing is exactly the unchanged original lifting condition with multiplier one. -/
theorem originalBoundaryObstruction_eq_zero_iff_one_mem (t : D) :
    originalBoundaryObstructionMap f hL d V c k W hW t = 0 ↔
      1 ∈ originalBoundaryLiftIdeal f hL d V c k W t := by
  unfold originalBoundaryObstructionMap
  rw [BoundaryCorrectionIdeal.originalBoundaryCokernelMap_eq_zero_iff]
  simp only [originalBoundaryCoefficientLinearMap_apply]
  have h := original_liftIdeal_mem_iff_numerators f hL d V c k W hW t 1
  unfold originalCorrectionBoundaryHom originalCorrectionFirstHom originalCorrectionSecondHom
  simpa only [AlgHom.coe_mk, map_one, one_mul] using h.symm

/-- A zero class has an actual original invariant lift, and every such lift has zero class. -/
theorem originalBoundaryObstruction_eq_zero_iff_lift (t : D) :
    originalBoundaryObstructionMap f hL d V c k W hW t = 0 ↔
      ∃ a : Ω, ρ a = t := by
  rw [originalBoundaryObstruction_eq_zero_iff_one_mem]
  change (∃ a : Ω, ρ a = ρ 1 * t) ↔ _
  rw [map_one, one_mul]

/-- The original closed pullback as a linear map over the original invariant ring. -/
def originalBoundaryPullbackLinearMap : Ω →ₗ[Ω] D :=
  Algebra.linearMap Ω D

attribute [local irreducible] originalBoundaryPullbackLinearMap

/-- The kernel is exactly the restrictions of actual original invariant sections. -/
theorem originalBoundaryObstruction_ker :
    LinearMap.ker (originalBoundaryObstructionMap f hL d V c k W hW) =
      LinearMap.range (originalBoundaryPullbackLinearMap f hL d V c k W) := by
  ext t
  rw [LinearMap.mem_ker, originalBoundaryObstruction_eq_zero_iff_lift]
  unfold originalBoundaryPullbackLinearMap
  rfl

/-- The actual original obstruction image is the boundary module modulo original restrictions. -/
def originalBoundaryObstructionQuotientEquiv :
    (D ⧸ LinearMap.range (originalBoundaryPullbackLinearMap f hL d V c k W)) ≃ₗ[Ω]
      LinearMap.range (originalBoundaryObstructionMap f hL d V c k W hW) :=
  (Submodule.quotEquivOfEq _ _
    (originalBoundaryObstruction_ker f hL d V c k W hW).symm).trans
      (originalBoundaryObstructionMap f hL d V c k W hW).quotKerEquivRange

end OrbitBoundaryAtlas.FiniteAtlas
end FLT.Mazur.HilbertChart.AffineRestriction
