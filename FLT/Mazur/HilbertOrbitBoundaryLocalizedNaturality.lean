/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.HilbertOrbitBoundaryLocalizedMaps

/-!
# Original coefficients under localized boundary and full mixed pullback

Each localized ring map extends its original coefficient map. These identities
allow denominator clearing without unfolding the geometric map constructions.
-/

public noncomputable section
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

open PrincipalLocalizationMap
local notation "ef" => fullRelationSchemeEquivalence f hL d V c k
local notation "n" => fun j : Charts ↦ j.val.size
local notation "o" => fun j : Charts ↦ j.val.label
local notation "U" => fun j : Charts ↦ j.val.domain
local notation "hU" => fun j : Charts ↦ j.val.stable
local notation "F" => MixedFrames.ChartFamily.firstCoefficientMap ef n o U hU
local notation "G" => MixedFrames.ChartFamily.secondCoefficientMap ef n o U hU
local notation "H" => fun j : Charts ↦ normalizedBoundaryChartMap f hL d V c k j.val.size
  j.val.label j.val.domain j.val.stable

variable (a : (invariantSheaf (equivalence f hL d V c k)).obj.obj (op W))
local notation "r" => scalarFamily f hL d V c k W hW a

/-- Localized boundary restriction retains every original invariant coefficient. -/
theorem localizedChartBoundaryMap_algebraMap (j : Charts)
    (x : chartCoordinateRing f hL d V c k W hW j) :
    localizedChartBoundaryMap f hL d V c k W hW a j (algebraMap _ _ x) =
      algebraMap _ _ (H j x) :=
  map_algebraMap (H j) (r j) (H j (r j)) rfl x

/-- First localized mixed pullback retains every original chart coefficient. -/
theorem localizedChartFirstMap_algebraMap (j l : Charts)
    (x : chartCoordinateRing f hL d V c k W hW j) :
    localizedChartFirstMap f hL d V c k W hW a j l (algebraMap _ _ x) =
      algebraMap _ _ (F j l x) :=
  map_algebraMap (F j l) (r j) (F j l (r j)) rfl x

/-- Second localized mixed pullback retains the independently indexed chart coefficient. -/
theorem localizedChartSecondMap_algebraMap (j l : Charts)
    (x : chartCoordinateRing f hL d V c k W hW l) :
    localizedChartSecondMap f hL d V c k W hW a j l (algebraMap _ _ x) =
      algebraMap _ _ (G j l x) :=
  map_algebraMap (G j l) (r l) (F j l (r j))
    (scalarFamily_compatible f hL d V c k W hW a j l).symm x

end OrbitBoundaryAtlas.FiniteAtlas
end FLT.Mazur.HilbertChart.AffineRestriction
