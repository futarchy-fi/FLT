/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.HilbertOrbitBoundaryLocalizedNumerators

/-!
# Original lifting multipliers constructed from localized finite chart solutions

Use the canonical compatible chart family of a specified original scalar.
Localized boundary lifts satisfying all localized full mixed equations give
an actual power of that scalar in the original lifting ideal. Neither exact
unlocalized chart compatibility nor kernel corrections are assumed.
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

variable (t : (invariantSheaf (originalClosedEquivalence f hL d V c k)).obj.obj
  (op ((TopologicalSpace.Opens.map (originalClosedInvariantMap f hL d V c k).base).obj W)))

variable (v : ∀ j : finiteCharts f hL d V c k W hW,
  Localization.Away (scalarFamily f hL d V c k W hW a j))

/-- The specified original scalar has a power in the unchanged original lifting ideal. -/
theorem original_multiplier_of_localized
    (hb : ∀ j : Charts, localizedChartBoundaryMap f hL d V c k W hW a j (v j) =
      algebraMap _ _ (normalizedOrbitBoundaryCoefficient f hL d V c k j.val.size j.val.label W
        j.val.domain j.val.stable j.val.overDomain t))
    (he : ∀ j l : Charts, localizedChartFirstMap f hL d V c k W hW a j l (v j) =
      localizedChartSecondMap f hL d V c k W hW a j l (v l)) :
    ∃ N : ℕ, a ^ N ∈ originalBoundaryLiftIdeal f hL d V c k W t := by
  obtain ⟨N, w, hb', hc⟩ := original_numerators_of_localized f hL d V c k W hW a t v hb he
  exact ⟨N, original_power_mem_of_scaled_boundary f hL d V c k W hW t a N w hb' hc⟩

/-- Localized compatible solutions place the actual original scalar in the lifting radical. -/
theorem original_radical_of_localized
    (hb : ∀ j : Charts, localizedChartBoundaryMap f hL d V c k W hW a j (v j) =
      algebraMap _ _ (normalizedOrbitBoundaryCoefficient f hL d V c k j.val.size j.val.label W
        j.val.domain j.val.stable j.val.overDomain t))
    (he : ∀ j l : Charts, localizedChartFirstMap f hL d V c k W hW a j l (v j) =
      localizedChartSecondMap f hL d V c k W hW a j l (v l)) :
    a ∈ (originalBoundaryLiftIdeal f hL d V c k W t).radical :=
  Ideal.mem_radical_iff.mpr
    (original_multiplier_of_localized f hL d V c k W hW a t v hb he)

/-- The specified nonvanishing scalar gives an actual original lifting neighborhood. -/
theorem original_principal_le_of_localized
    (hb : ∀ j : Charts, localizedChartBoundaryMap f hL d V c k W hW a j (v j) =
      algebraMap _ _ (normalizedOrbitBoundaryCoefficient f hL d V c k j.val.size j.val.label W
        j.val.domain j.val.stable j.val.overDomain t))
    (he : ∀ j l : Charts, localizedChartFirstMap f hL d V c k W hW a j l (v j) =
      localizedChartSecondMap f hL d V c k W hW a j l (v l)) :
    invariantPrincipal e W a ≤ originalBoundaryLiftOpen f hL d V c k W t := by
  intro x hx
  apply (mem_originalBoundaryLiftOpen_iff f hL d V c k W t hW x).mpr
  refine ⟨a, hx, ?_⟩
  exact (originalBoundaryLiftIdeal_radical_iff f hL d V c k W t hW a).mp
    (original_radical_of_localized f hL d V c k W hW a t v hb he)

end OrbitBoundaryAtlas.FiniteAtlas
end FLT.Mazur.HilbertChart.AffineRestriction
