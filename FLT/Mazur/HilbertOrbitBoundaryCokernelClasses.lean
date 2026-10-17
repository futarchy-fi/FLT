/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.HilbertOrbitBoundaryFlatObstruction

/-!
# A sealed full cokernel for actual boundary classes

Naming the cokernel and its module structures keeps subsequent scalar-error
identities from repeatedly expanding the full geometric coordinate types.
The definitions retain exactly the original full correction quotient.
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


/-- The unchanged full ambient correction cokernel, named before its use in class identities. -/
def originalBoundaryExtendedCokernel : Type _ :=
  (S ⊗[Ω] ((∀ j : Charts, Bc j) × ∀ j l : Charts, Cc j l)) ⧸ LinearMap.range F₀

instance originalBoundaryExtendedCokernelAddCommGroup :
    AddCommGroup (originalBoundaryExtendedCokernel f hL d V c k W hW S) :=
  inferInstanceAs (AddCommGroup
    ((S ⊗[Ω] ((∀ j : Charts, Bc j) × ∀ j l : Charts, Cc j l)) ⧸ LinearMap.range F₀))

instance originalBoundaryExtendedCokernelModule :
    Module S (originalBoundaryExtendedCokernel f hL d V c k W hW S) :=
  inferInstanceAs (Module S
    ((S ⊗[Ω] ((∀ j : Charts, Bc j) × ∀ j l : Charts, Cc j l)) ⧸ LinearMap.range F₀))

/-- The actual extended obstruction map with its named full cokernel as codomain. -/
def originalBoundarySealedObstructionMap :
    (S ⊗[Ω] D) →ₗ[S] originalBoundaryExtendedCokernel f hL d V c k W hW S :=
  originalBoundaryExtendedObstructionMap f hL d V c k W hW S

/-- The scalar error of the chosen lifts in the named full cokernel. -/
def originalBoundaryLiftErrorClass (t : D) :
    originalBoundaryExtendedCokernel f hL d V c k W hW S :=
  π (BoundaryCorrectionIdeal.ambientScalarError Hb Fp Gq
    (lifts f hL d V c k W hW t) S)

attribute [irreducible] originalBoundaryExtendedCokernel

end OrbitBoundaryAtlas.FiniteAtlas
end FLT.Mazur.HilbertChart.AffineRestriction
