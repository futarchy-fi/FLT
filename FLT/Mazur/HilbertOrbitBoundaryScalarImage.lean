/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.HilbertOrbitBoundaryCokernelClasses

/-!
# The actual scalar errors generate the sealed boundary image

The canonical coefficient map carries each original boundary section to the
class of its actual chosen-lift scalar error. Naming the full cokernel keeps
this identity small while preserving every mixed correction equation.
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

/-- The actual chosen-lift scalar class is the image of the original boundary parameter. -/
theorem originalBoundarySealedObstruction_scalar (t : D) :
    originalBoundarySealedObstructionMap f hL d V c k W hW S (1 ⊗ₜ[Ω] t) =
      originalBoundaryLiftErrorClass f hL d V c k W hW S t := by
  unfold originalBoundarySealedObstructionMap originalBoundaryLiftErrorClass
    originalBoundaryExtendedObstructionMap originalBoundaryExtendedCokernel
    originalBoundaryExtendedCokernelAddCommGroup originalBoundaryExtendedCokernelModule
  exact BoundaryCorrectionIdeal.boundaryCokernelMap_one_tmul Hb Fp Gq 0 β S t _
    (originalBoundaryCoefficientLinearMap_lifts f hL d V c k W hW t)

/-- The actual image is exactly the span of the actual scalar errors of boundary sections. -/
theorem originalBoundarySealedObstruction_range :
    LinearMap.range (originalBoundarySealedObstructionMap f hL d V c k W hW S) =
      Submodule.span S (Set.range (originalBoundaryLiftErrorClass f hL d V c k W hW S)) := by
  apply le_antisymm
  · rintro _ ⟨x, rfl⟩
    induction x using TensorProduct.inductionOn with
    | tmul s t =>
      have ht : originalBoundarySealedObstructionMap f hL d V c k W hW S (1 ⊗ₜ[Ω] t) ∈
          Submodule.span S
            (Set.range (originalBoundaryLiftErrorClass f hL d V c k W hW S)) := by
        rw [originalBoundarySealedObstruction_scalar]
        exact Submodule.subset_span (Set.mem_range_self t)
      have hs := Submodule.smul_mem _ s ht
      simpa only [← map_smul, smul_tmul', smul_eq_mul, mul_one] using hs
    | add x y hx hy => simpa only [map_add] using Submodule.add_mem _ hx hy
  · apply Submodule.span_le.mpr
    rintro _ ⟨t, rfl⟩
    exact ⟨1 ⊗ₜ[Ω] t, originalBoundarySealedObstruction_scalar f hL d V c k W hW S t⟩

/-- Every specified scalar error belongs to the actual boundary obstruction image. -/
theorem originalBoundaryLiftErrorClass_mem_range (t : D) :
    originalBoundaryLiftErrorClass f hL d V c k W hW S t ∈
      LinearMap.range (originalBoundarySealedObstructionMap f hL d V c k W hW S) :=
  ⟨1 ⊗ₜ[Ω] t, originalBoundarySealedObstruction_scalar f hL d V c k W hW S t⟩

end OrbitBoundaryAtlas.FiniteAtlas
end FLT.Mazur.HilbertChart.AffineRestriction
