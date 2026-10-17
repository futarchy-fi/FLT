/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.HilbertOrbitBoundaryCorrectionIdeal
public import FLT.Mazur.HilbertMixedResidualBranches
public import FLT.Mazur.EquivalenceRelationMixedBranchCoefficients
public import FLT.Mazur.BoundaryCorrectionFaithfulCoefficients

/-!
# The unchanged original lifting ideal in independent mixed branch coordinates

Use the actual Hilbert source separatedness to split every full mixed chart
coefficient ring. The product retains the residual factor and all independently
labeled embedding factors. The resulting correction ideal equals W351's ideal
and hence the original lifting ideal; no branch equations are discarded.
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
variable (t : (invariantSheaf (originalClosedEquivalence f hL d V c k)).obj.obj
  (op ((TopologicalSpace.Opens.map (originalClosedInvariantMap f hL d V c k).base).obj W)))

/-- Compute full corrections using all residual and independent embedding coefficients. -/
def originalMixedBranchCorrectionIdeal : Ideal ((invariantSheaf e).obj.obj (op W)) := by
  let _ : ∀ j : Charts, (source (Over.Hom.left (AffineRestriction.fst f hL d V c k))
      (Over.Hom.left (AffineRestriction.snd f hL d V c k)) (Fin (n j)) (o j)).IsSeparated :=
    fun j ↦ normalizedFrameSource_separated f hL d V c k (n j) (o j)
  let ψ j l := MixedFrames.mixedBranchCoefficientMap ef (o j) (o l) (U j) (U l)
  exact BoundaryCorrectionIdeal.ideal α H
    (fun j l ↦ (ψ j l).comp (F j l)) (fun j l ↦ (ψ j l).comp (G j l))
    (BoundaryCorrectionIdeal.faithful_scalar_compatible α F G
      (originalChartScalarMap_full_compatible f hL d V c k W hW) ψ)
    (lifts f hL d V c k W hW t)

/-- Branch testing preserves the full independent correction ideal exactly. -/
theorem originalMixedBranchCorrectionIdeal_eq_original :
    originalMixedBranchCorrectionIdeal f hL d V c k W hW t =
      originalCorrectionIdeal f hL d V c k W hW t := by
  let _ : ∀ j : Charts, (source (Over.Hom.left (AffineRestriction.fst f hL d V c k))
      (Over.Hom.left (AffineRestriction.snd f hL d V c k)) (Fin (n j)) (o j)).IsSeparated :=
    fun j ↦ normalizedFrameSource_separated f hL d V c k (n j) (o j)
  exact (BoundaryCorrectionIdeal.ideal_eq_faithful α H F G
    (originalChartScalarMap_full_compatible f hL d V c k W hW)
    (fun j l ↦ MixedFrames.mixedBranchCoefficientMap ef (o j) (o l) (U j) (U l))
    (fun j l ↦ (MixedFrames.mixedBranchCoefficientMap_bijective
      ef (o j) (o l) (U j) (U l)).injective)
    (lifts f hL d V c k W hW t)).symm

/-- The result remains an ideal in original invariant source scalars, with exact lifting meaning. -/
theorem originalMixedBranchCorrectionIdeal_eq_liftIdeal :
    originalMixedBranchCorrectionIdeal f hL d V c k W hW t =
      originalBoundaryLiftIdeal f hL d V c k W t :=
  (originalMixedBranchCorrectionIdeal_eq_original f hL d V c k W hW t).trans
    (originalCorrectionIdeal_eq_liftIdeal f hL d V c k W hW t)

end OrbitBoundaryAtlas.FiniteAtlas
end FLT.Mazur.HilbertChart.AffineRestriction
