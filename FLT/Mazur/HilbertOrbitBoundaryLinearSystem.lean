/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.HilbertOrbitBoundaryCorrectionIdeal
public import FLT.Mazur.BoundaryCorrectionFlatDescent

/-!
# The actual Hilbert boundary correction system over original scalars

The exact chart, boundary, and full mixed coefficient rings receive their
original scalar algebras. Their original maps become algebra homomorphisms,
so the full simultaneous correction problem is an actual linear kernel.
-/

@[expose] public noncomputable section
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry Opposite
namespace FLT.Mazur.HilbertChart.AffineRestriction
open CartierAbel SchemePicard FCurve EquivalenceRelationNormalizedFrames
open RelativeRelationOrbit InvariantOpenRelationDiagram
open FiniteGroupRestriction SchemeFiniteGroupQuotient
set_option backward.isDefEq.respectTransparency false
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

open BaseLocalizationMap
local notation "ef" => fullRelationSchemeEquivalence f hL d V c k
local notation "n" => fun j : Charts ↦ j.val.size
local notation "o" => fun j : Charts ↦ j.val.label
local notation "U" => fun j : Charts ↦ j.val.domain
local notation "hU" => fun j : Charts ↦ j.val.stable
local notation "F" => MixedFrames.ChartFamily.firstCoefficientMap ef n o U hU
local notation "G" => MixedFrames.ChartFamily.secondCoefficientMap ef n o U hU
local notation "H" => fun j : Charts ↦ normalizedBoundaryChartMap f hL d V c k j.val.size
  j.val.label j.val.domain j.val.stable

attribute [local irreducible] originalChartScalarMap
local notation "α" => originalChartScalarMap f hL d V c k W hW
local notation "Ω" => (invariantSheaf e).obj.obj (op W)
local notation "Ac" => chartCoordinateRing f hL d V c k W hW
local notation "Bc" => chartBoundaryCoordinateRing f hL d V c k W hW
local notation "Cc" => mixedCoordinateRing f hL d V c k W hW

/-- Original invariant scalars act on each original chart coefficient ring. -/
@[instance_reducible]
def originalCorrectionChartAlgebra (j : Charts) : Algebra Ω (Ac j) := (α j).toAlgebra

/-- Original invariant scalars act on each exact boundary coefficient ring. -/
@[instance_reducible]
def originalCorrectionBoundaryAlgebra (j : Charts) : Algebra Ω (Bc j) :=
  ((H j).comp (α j)).toAlgebra

/-- Original invariant scalars act on each full independent mixed relation ring. -/
@[instance_reducible]
def originalCorrectionMixedAlgebra (j l : Charts) : Algebra Ω (Cc j l) :=
  ((F j l).comp (α j)).toAlgebra

attribute [local instance] originalCorrectionChartAlgebra originalCorrectionBoundaryAlgebra
  originalCorrectionMixedAlgebra

/-- The unchanged boundary map is linear over the original scalars. -/
def originalCorrectionBoundaryHom (j : Charts) : Ac j →ₐ[Ω] Bc j where
  __ := H j
  commutes' _ := rfl

/-- The original first coefficient map is linear over original scalars. -/
def originalCorrectionFirstHom (j l : Charts) : Ac j →ₐ[Ω] Cc j l where
  __ := F j l
  commutes' _ := rfl

/-- The independently labeled second map has the same original scalar action. -/
def originalCorrectionSecondHom (j l : Charts) : Ac l →ₐ[Ω] Cc j l where
  __ := G j l
  commutes' a := (originalChartScalarMap_full_compatible f hL d V c k W hW j l a).symm

local notation "Hb" => originalCorrectionBoundaryHom f hL d V c k W hW
local notation "Fp" => originalCorrectionFirstHom f hL d V c k W hW
local notation "Gq" => originalCorrectionSecondHom f hL d V c k W hW
variable (t : (invariantSheaf (originalClosedEquivalence f hL d V c k)).obj.obj
  (op ((TopologicalSpace.Opens.map (originalClosedInvariantMap f hL d V c k).base).obj W)))
local notation "u" => lifts f hL d V c k W hW t

/-- One linear map contains all original boundary and full mixed correction equations. -/
def originalCorrectionSystem : (Ω × ∀ j : Charts, Ac j) →ₗ[Ω]
    ((∀ j : Charts, Bc j) × ∀ j l : Charts, Cc j l) :=
  BoundaryCorrectionIdeal.correctionSystem Hb Fp Gq u

/-- The system's kernel projects onto exactly the original lifting ideal. -/
theorem originalCorrectionSystem_multiplier_range :
    LinearMap.range (BoundaryCorrectionIdeal.correctionMultiplier Hb Fp Gq u) =
      originalBoundaryLiftIdeal f hL d V c k W t := by
  rw [BoundaryCorrectionIdeal.range_correctionMultiplier]
  exact originalCorrectionIdeal_eq_liftIdeal f hL d V c k W hW t

end OrbitBoundaryAtlas.FiniteAtlas
end FLT.Mazur.HilbertChart.AffineRestriction
