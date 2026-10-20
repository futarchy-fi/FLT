/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.HilbertOrbitBoundaryScalarImage
public import FLT.Mazur.HilbertLocallyFreeTraceUnit
public import FLT.Mazur.BoundaryCorrectionScalarVanishing

/-!
# Finite-domain error vanishing after arbitrary scalar extension

Surjectivity on full finite original domains kills the entire boundary
obstruction map after every scalar extension, including nonflat extensions.
No assertion is made that its full correction cokernel vanishes.
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

variable (hfin : (pullOpen (equivalence f hL d V c k) W).val ≤
    SchemeOpenEnvelope.finiteTargetOpen (AffineRestriction.fst f hL d V c k).left)

include hfin in
/-- Exact original lifts make the full original boundary obstruction map zero. -/
theorem originalBoundaryObstructionMap_eq_zero_of_finite_domain :
    originalBoundaryObstructionMap f hL d V c k W hW = 0 := by
  ext t
  apply (originalBoundaryObstruction_eq_zero_iff_lift f hL d V c k W hW t).mpr
  exact originalClosedSectionPullback_surjective_of_finite_domain f hL d V c k W hW hfin t

include hfin in
set_option backward.isDefEq.respectTransparency false in
/-- Every scalar extension retains exact vanishing of the actual boundary obstruction map. -/
theorem originalBoundarySealedObstructionMap_eq_zero_of_finite_domain :
    originalBoundarySealedObstructionMap f hL d V c k W hW S = 0 := by
  apply LinearMap.ext
  intro x
  change originalBoundarySealedObstructionMap f hL d V c k W hW S x = 0
  unfold originalBoundarySealedObstructionMap originalBoundaryExtendedObstructionMap
    originalBoundaryExtendedCokernel originalBoundaryExtendedCokernelAddCommGroup
    originalBoundaryExtendedCokernelModule
  exact LinearMap.congr_fun
    (BoundaryCorrectionIdeal.boundaryCokernelMap_eq_zero_of_original Hb Fp Gq 0 β S
      (originalBoundaryObstructionMap_eq_zero_of_finite_domain f hL d V c k W hW hfin)) x

include hfin in
/-- Every original scalar error is zero over arbitrary, possibly nonflat, coefficients. -/
theorem originalBoundaryLiftErrorClass_eq_zero_of_finite_domain (t : D) :
    originalBoundaryLiftErrorClass f hL d V c k W hW S t = 0 := by
  rw [← originalBoundarySealedObstruction_scalar,
    originalBoundarySealedObstructionMap_eq_zero_of_finite_domain
      f hL d V c k W hW S hfin, LinearMap.zero_apply]

end OrbitBoundaryAtlas.FiniteAtlas
end FLT.Mazur.HilbertChart.AffineRestriction
