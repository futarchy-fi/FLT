/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.HilbertOrbitBoundaryBaseLocalizedMultipliers
public import FLT.Mazur.RelativeRelationPointDenominators

/-!
# Constructing nonvanishing original multipliers from point-localized solutions

Localize the actual finite atlas at all original invariant sections nonvanishing
at a specified orbit point. Compatible solutions there construct one original
nonvanishing scalar, exact numerators, and a principal lifting neighborhood.
Existence of these localized solutions is still a separate geometric task.
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

variable (x : Orbit (equivalence f hL d V c k)) (hx : x ∈ W)
attribute [local irreducible] pointDenominators originalChartScalarMap
  baseLocalizedBoundaryMap baseLocalizedFirstMap baseLocalizedSecondMap
local notation "M" => pointDenominators e W x hx
variable (t : (invariantSheaf (originalClosedEquivalence f hL d V c k)).obj.obj
  (op ((TopologicalSpace.Opens.map (originalClosedInvariantMap f hL d V c k).base).obj W)))
variable (v : ∀ j : finiteCharts f hL d V c k W hW,
  baseLocalizedChartRing f hL d V c k W hW
    (pointDenominators (equivalence f hL d V c k) W x hx) j)

/-- Point-localized full compatibility constructs an original nonvanishing lifting multiplier. -/
theorem original_nonvanishing_multiplier_of_point_localized
    (hb : ∀ j : Charts, baseLocalizedBoundaryMap f hL d V c k W hW M j (v j) =
      algebraMap _ _ (normalizedOrbitBoundaryCoefficient f hL d V c k j.val.size j.val.label W
        j.val.domain j.val.stable j.val.overDomain t))
    (he : ∀ j l : Charts, baseLocalizedFirstMap f hL d V c k W hW M j l (v j) =
      baseLocalizedSecondMap f hL d V c k W hW M j l (v l)) :
    ∃ a : (invariantSheaf e).obj.obj (op W),
      x ∈ invariantPrincipal e W a ∧ a ∈ originalBoundaryLiftIdeal f hL d V c k W t := by
  obtain ⟨a, ha⟩ := original_multiplier_of_base_localized f hL d V c k W hW M t v hb he
  exact ⟨a.val, (pointDenominator_mem e W x hx a), ha⟩

/-- Point-localized solutions give a genuine affine-source principal lifting neighborhood. -/
theorem original_neighborhood_of_point_localized
    (hb : ∀ j : Charts, baseLocalizedBoundaryMap f hL d V c k W hW M j (v j) =
      algebraMap _ _ (normalizedOrbitBoundaryCoefficient f hL d V c k j.val.size j.val.label W
        j.val.domain j.val.stable j.val.overDomain t))
    (he : ∀ j l : Charts, baseLocalizedFirstMap f hL d V c k W hW M j l (v j) =
      baseLocalizedSecondMap f hL d V c k W hW M j l (v l)) :
    ∃ a : (invariantSheaf e).obj.obj (op W),
      x ∈ invariantPrincipal e W a ∧
      IsAffineOpen (pullOpen e (invariantPrincipal e W a)).val ∧
      invariantPrincipal e W a ≤ originalBoundaryLiftOpen f hL d V c k W t := by
  obtain ⟨a, ha⟩ := original_principal_of_base_localized f hL d V c k W hW M t v hb he
  exact ⟨a.val, pointDenominator_mem e W x hx a,
    invariantPrincipal_source_affine e W hW a.val, ha⟩

end OrbitBoundaryAtlas.FiniteAtlas
end FLT.Mazur.HilbertChart.AffineRestriction
