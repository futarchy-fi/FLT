/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.HilbertOrbitBoundaryBaseLocalizationMaps
public import FLT.Mazur.FiniteBaseLocalizedBoundaryLifts

/-!
# Original lifting multipliers constructed from arbitrary base-localized solutions

The original scalar is now constructed in a prescribed multiplicative set.
Compatible solutions localized at its images on the actual finite atlas give
exact original numerators and an element of the original boundary lifting ideal.
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
variable (M : Submonoid ((invariantSheaf (equivalence f hL d V c k)).obj.obj (op W)))
variable (t : (invariantSheaf (originalClosedEquivalence f hL d V c k)).obj.obj
  (op ((TopologicalSpace.Opens.map (originalClosedInvariantMap f hL d V c k).base).obj W)))
variable (v : ∀ j : finiteCharts f hL d V c k W hW,
  baseLocalizedChartRing f hL d V c k W hW M j)

/-- Base-localized compatible solutions construct a scalar and exact original chart numerators. -/
theorem original_numerators_of_base_localized
    (hb : ∀ j : Charts, baseLocalizedBoundaryMap f hL d V c k W hW M j (v j) =
      algebraMap _ _ (normalizedOrbitBoundaryCoefficient f hL d V c k j.val.size j.val.label W
        j.val.domain j.val.stable j.val.overDomain t))
    (he : ∀ j l : Charts, baseLocalizedFirstMap f hL d V c k W hW M j l (v j) =
      baseLocalizedSecondMap f hL d V c k W hW M j l (v l)) :
    ∃ s : M, ∃ w : Sections f hL d V c k W hW,
      (∀ j : Charts, H j (w j) = H j (α j s) *
        normalizedOrbitBoundaryCoefficient f hL d V c k j.val.size j.val.label W
          j.val.domain j.val.stable j.val.overDomain t) ∧
      (∀ j l : Charts, F j l (w j) = G j l (w l)) :=
  FiniteBaseLocalizedBoundaryLifts.exists_exact_numerators
    (A := chartCoordinateRing f hL d V c k W hW)
    (B := chartBoundaryCoordinateRing f hL d V c k W hW)
    (C := mixedCoordinateRing f hL d V c k W hW) M α H F G
    (fun j l a ↦ by
      simpa only [originalChartScalarMap_apply, MixedFrames.ChartFamily.firstCoefficientMap,
        MixedFrames.ChartFamily.secondCoefficientMap, RingHom.comp_apply, Subring.subtype_apply,
        CommRingCat.Hom.hom] using
        scalarFamily_compatible f hL d V c k W hW a j l)
    (baseLocalizedBoundaryMap f hL d V c k W hW M)
    (baseLocalizedFirstMap f hL d V c k W hW M)
    (baseLocalizedSecondMap f hL d V c k W hW M)
    (baseLocalizedBoundaryMap_algebraMap f hL d V c k W hW M)
    (baseLocalizedFirstMap_algebraMap f hL d V c k W hW M)
    (baseLocalizedSecondMap_algebraMap f hL d V c k W hW M) v
    (fun j ↦ normalizedOrbitBoundaryCoefficient f hL d V c k j.val.size j.val.label W
      j.val.domain j.val.stable j.val.overDomain t) hb he

/-- A constructed allowed original scalar belongs to the unchanged original lifting ideal. -/
theorem original_multiplier_of_base_localized
    (hb : ∀ j : Charts, baseLocalizedBoundaryMap f hL d V c k W hW M j (v j) =
      algebraMap _ _ (normalizedOrbitBoundaryCoefficient f hL d V c k j.val.size j.val.label W
        j.val.domain j.val.stable j.val.overDomain t))
    (he : ∀ j l : Charts, baseLocalizedFirstMap f hL d V c k W hW M j l (v j) =
      baseLocalizedSecondMap f hL d V c k W hW M j l (v l)) :
    ∃ s : M, s.val ∈ originalBoundaryLiftIdeal f hL d V c k W t := by
  obtain ⟨s, w, hb', hc⟩ :=
    original_numerators_of_base_localized f hL d V c k W hW M t v hb he
  refine ⟨s, ?_⟩
  have h := original_power_mem_of_scaled_boundary f hL d V c k W hW t s.val 1 w
    (fun j ↦ by simpa only [pow_one, ← originalChartScalarMap_apply] using hb' j) hc
  simpa only [pow_one] using h

/-- The constructed scalar gives an actual original principal lifting neighborhood. -/
theorem original_principal_of_base_localized
    (hb : ∀ j : Charts, baseLocalizedBoundaryMap f hL d V c k W hW M j (v j) =
      algebraMap _ _ (normalizedOrbitBoundaryCoefficient f hL d V c k j.val.size j.val.label W
        j.val.domain j.val.stable j.val.overDomain t))
    (he : ∀ j l : Charts, baseLocalizedFirstMap f hL d V c k W hW M j l (v j) =
      baseLocalizedSecondMap f hL d V c k W hW M j l (v l)) :
    ∃ s : M, invariantPrincipal e W s.val ≤ originalBoundaryLiftOpen f hL d V c k W t := by
  obtain ⟨s, hs⟩ := original_multiplier_of_base_localized f hL d V c k W hW M t v hb he
  refine ⟨s, fun x hx ↦ ?_⟩
  apply (mem_originalBoundaryLiftOpen_iff f hL d V c k W t hW x).mpr
  refine ⟨s.val, hx, ?_⟩
  exact (originalBoundaryLiftIdeal_radical_iff f hL d V c k W t hW s.val).mp
    (Ideal.le_radical hs)

end OrbitBoundaryAtlas.FiniteAtlas
end FLT.Mazur.HilbertChart.AffineRestriction
