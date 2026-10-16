/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.HilbertOrbitBoundaryBaseLocalizationMaps
public import FLT.Mazur.FiniteBaseLocalizedKernels

/-!
# Actual localized boundary lifts and exact correction numerators

The chosen original chart lifts give lifts in every base localization. Any
other lifts of those same boundary values differ by fractions whose numerators
are in the exact original chart boundary kernels, with one common denominator.
The full mixed compatibility equations remain a separate constraint.
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
  baseLocalizedBoundaryMap baseLocalizedFirstMap baseLocalizedSecondMap
local notation "α" => originalChartScalarMap f hL d V c k W hW
variable (M : Submonoid ((invariantSheaf (equivalence f hL d V c k)).obj.obj (op W)))
variable (t : (invariantSheaf (originalClosedEquivalence f hL d V c k)).obj.obj
  (op ((TopologicalSpace.Opens.map (originalClosedInvariantMap f hL d V c k).base).obj W)))
/-- The original chosen lifts in the actual localized chart rings. -/
def baseLocalizedLifts (j : Charts) : baseLocalizedChartRing f hL d V c k W hW M j :=
  algebraMap _ _ (lifts f hL d V c k W hW t j)

/-- These lifts have precisely the original localized boundary coefficients. -/
theorem baseLocalizedLifts_boundary (j : Charts) :
    baseLocalizedBoundaryMap f hL d V c k W hW M j
      (baseLocalizedLifts f hL d V c k W hW M t j) =
        algebraMap _ _ (normalizedOrbitBoundaryCoefficient f hL d V c k j.val.size j.val.label
          W j.val.domain j.val.stable j.val.overDomain t) := by
  exact (baseLocalizedBoundaryMap_algebraMap f hL d V c k W hW M j
    (lifts f hL d V c k W hW t j)).trans
      (congrArg (algebraMap (chartBoundaryCoordinateRing f hL d V c k W hW j)
        (baseLocalizedBoundaryRing f hL d V c k W hW M j))
        (lifts_restrict f hL d V c k W hW t j))

attribute [local irreducible] baseLocalizedLifts

/-- Every family in the actual localized boundary kernels has exact original kernel numerators. -/
theorem baseLocalized_kernel_numerators
    (v : ∀ j : Charts, baseLocalizedChartRing f hL d V c k W hW M j)
    (hv : ∀ j : Charts, baseLocalizedBoundaryMap f hL d V c k W hW M j (v j) = 0) :
    ∃ s : M, ∃ z : Sections f hL d V c k W hW,
      (∀ j : Charts, H j (z j) = 0) ∧
      ∀ j : Charts, algebraMap _ (baseLocalizedChartRing f hL d V c k W hW M j) (z j) =
        algebraMap _ _ (α j s) * v j :=
  FiniteBaseLocalizedKernels.exists_kernel_numerators
    (A := chartCoordinateRing f hL d V c k W hW)
    (B := chartBoundaryCoordinateRing f hL d V c k W hW) M α H
    (baseLocalizedBoundaryMap f hL d V c k W hW M)
    (baseLocalizedBoundaryMap_algebraMap f hL d V c k W hW M) v hv

/-- Every alternative localized boundary lift is a correction by exact original kernel fractions. -/
theorem baseLocalized_lift_correction_numerators
    (v : ∀ j : Charts, baseLocalizedChartRing f hL d V c k W hW M j)
    (hv : ∀ j : Charts, baseLocalizedBoundaryMap f hL d V c k W hW M j (v j) =
      algebraMap _ _ (normalizedOrbitBoundaryCoefficient f hL d V c k j.val.size j.val.label
        W j.val.domain j.val.stable j.val.overDomain t)) :
    ∃ s : M, ∃ z : Sections f hL d V c k W hW,
      (∀ j : Charts, H j (z j) = 0) ∧
      ∀ j : Charts, algebraMap _ (baseLocalizedChartRing f hL d V c k W hW M j) (z j) =
        algebraMap _ _ (α j s) * (baseLocalizedLifts f hL d V c k W hW M t j - v j) := by
  apply baseLocalized_kernel_numerators f hL d V c k W hW M
  intro j
  exact (map_sub (baseLocalizedBoundaryMap f hL d V c k W hW M j)
    (baseLocalizedLifts f hL d V c k W hW M t j) (v j)).trans
      (sub_eq_zero.mpr ((baseLocalizedLifts_boundary f hL d V c k W hW M t j).trans
        (hv j).symm))

end OrbitBoundaryAtlas.FiniteAtlas
end FLT.Mazur.HilbertChart.AffineRestriction
