/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.HilbertOrbitBoundaryLocalizedNaturality
public import FLT.Mazur.PrincipalBoundaryNumeratorSolutions

/-!
# Principal localized Hilbert lifts from exact original numerators

Divide exact compatible numerators by their common original scalar power.
The resulting coefficients solve the actual localized boundary and full mixed
relation equations on the selected finite atlas.
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
variable (t : (invariantSheaf (originalClosedEquivalence f hL d V c k)).obj.obj
  (op ((TopologicalSpace.Opens.map (originalClosedInvariantMap f hL d V c k).base).obj W)))

/-- Exact original numerators give solutions on the specified original principal localization. -/
theorem principal_solutions_of_original_numerators (w : Sections f hL d V c k W hW) (N : ℕ)
    (hb : ∀ j : Charts, H j (w j) = H j (r j) ^ N *
      normalizedOrbitBoundaryCoefficient f hL d V c k j.val.size j.val.label W
        j.val.domain j.val.stable j.val.overDomain t)
    (he : ∀ j l : Charts, F j l (w j) = G j l (w l)) :
    ∃ z : ∀ j : Charts, Localization.Away (r j),
      (∀ j : Charts, localizedChartBoundaryMap f hL d V c k W hW a j (z j) =
        algebraMap _ _ (normalizedOrbitBoundaryCoefficient f hL d V c k j.val.size
          j.val.label W j.val.domain j.val.stable j.val.overDomain t)) ∧
      (∀ j l : Charts, localizedChartFirstMap f hL d V c k W hW a j l (z j) =
        localizedChartSecondMap f hL d V c k W hW a j l (z l)) :=
  FiniteLocalizedBoundaryLifts.exists_localized_of_numerators
    (A := chartCoordinateRing f hL d V c k W hW)
    (B := chartBoundaryCoordinateRing f hL d V c k W hW)
    (C := mixedCoordinateRing f hL d V c k W hW) H F G r
    (scalarFamily_compatible f hL d V c k W hW a)
    (localizedChartBoundaryMap f hL d V c k W hW a)
    (localizedChartFirstMap f hL d V c k W hW a)
    (localizedChartSecondMap f hL d V c k W hW a)
    (localizedChartBoundaryMap_algebraMap f hL d V c k W hW a)
    (localizedChartFirstMap_algebraMap f hL d V c k W hW a)
    (localizedChartSecondMap_algebraMap f hL d V c k W hW a) w
    (fun j ↦ normalizedOrbitBoundaryCoefficient f hL d V c k j.val.size j.val.label W
      j.val.domain j.val.stable j.val.overDomain t) N hb he

end OrbitBoundaryAtlas.FiniteAtlas
end FLT.Mazur.HilbertChart.AffineRestriction
