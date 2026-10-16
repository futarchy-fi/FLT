/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.HilbertOrbitBoundaryFiniteProducts
public import FLT.Mazur.EquivalenceRelationFiniteChartMultipliers

/-!
# Original lifting multipliers from torsion on a finite atlas

A compatible scalar family descends to an original invariant scalar. When its
powers kill the finitely many full mixed discrepancies of actual boundary
lifts, one power is an actual original lifting multiplier. This permits local
multipliers without assuming that the original boundary section globally lifts.
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
local notation "e" => equivalence f hL d V c k
variable (W : TopologicalSpace.Opens (Orbit (equivalence f hL d V c k)))
set_option quotPrecheck false
local notation "E" => (pullOpen e W).val

variable (hW : IsAffineOpen (pullOpen (equivalence f hL d V c k) W).val)
local notation "C" => finiteCharts f hL d V c k W hW

variable (t : (invariantSheaf (originalClosedEquivalence f hL d V c k)).obj.obj
  (op ((TopologicalSpace.Opens.map (originalClosedInvariantMap f hL d V c k).base).obj W)))

local notation "φ" => originalClosedSectionPullback f hL d V c k W

/-- A specified original scalar obtains a numerator from compatible power-multiplied charts. -/
theorem original_power_mem_of_chart_values (u v : Sections f hL d V c k W hW)
    (hvBoundary : ∀ j : C,
      normalizedBoundaryChartMap f hL d V c k j.val.size j.val.label j.val.domain j.val.stable
        (v j) = normalizedOrbitBoundaryCoefficient f hL d V c k j.val.size j.val.label W
          j.val.domain j.val.stable j.val.overDomain t)
    (a : (invariantSheaf e).obj.obj (op W))
    (ha : ∀ j : C, (chartMap f hL d V c k W j.val).appTop
      (orbitFunctions e W a).val = (u j).val)
    (N : ℕ) (hN : ∀ a b : C,
      (MixedFrames.mixedChartFirst a.val.label b.val.label a.val.domain b.val.domain).appTop
        ((u a ^ N * v a).val) =
      (MixedFrames.mixedChartSecond a.val.label b.val.label a.val.domain b.val.domain).appTop
        ((u b ^ N * v b).val)) :
    a ^ N ∈ originalBoundaryLiftIdeal f hL d V c k W t := by
  let w : Sections f hL d V c k W hW := fun j ↦ u j ^ N * v j
  obtain ⟨b, hb⟩ := original_section_of_compatible f hL d V c k W hW (fun j ↦ (w j).val) hN
  have hboundary := descended_power_boundary f hL d V c k W hW t u v hvBoundary a b N ha hb
  change ∃ b, φ b = φ (a ^ N) * t
  refine ⟨b, ?_⟩
  rw [map_pow]
  exact original_boundary_power f hL d V c k W t a b N hboundary

/-- One compatible power multiple descends to an actual original numerator and multiplier. -/
theorem original_multiplier_of_compatible_power (u v : Sections f hL d V c k W hW)
    (hvBoundary : ∀ j : C,
      normalizedBoundaryChartMap f hL d V c k j.val.size j.val.label j.val.domain j.val.stable
        (v j) = normalizedOrbitBoundaryCoefficient f hL d V c k j.val.size j.val.label W
          j.val.domain j.val.stable j.val.overDomain t)
    (hu : ∀ a b : C,
      (MixedFrames.mixedChartFirst a.val.label b.val.label a.val.domain b.val.domain).appTop
        (u a).val =
      (MixedFrames.mixedChartSecond a.val.label b.val.label a.val.domain b.val.domain).appTop
        (u b).val)
    (N : ℕ) (hN : ∀ a b : C,
      (MixedFrames.mixedChartFirst a.val.label b.val.label a.val.domain b.val.domain).appTop
        ((u a ^ N * v a).val) =
      (MixedFrames.mixedChartSecond a.val.label b.val.label a.val.domain b.val.domain).appTop
        ((u b ^ N * v b).val)) :
    ∃ a : (invariantSheaf e).obj.obj (op W),
      (∀ j : C, (chartMap f hL d V c k W j.val).appTop
        (orbitFunctions e W a).val = (u j).val) ∧
      a ^ N ∈ originalBoundaryLiftIdeal f hL d V c k W t := by
  obtain ⟨a, ha⟩ := original_section_of_compatible f hL d V c k W hW (fun j ↦ (u j).val) hu
  exact ⟨a, ha, original_power_mem_of_chart_values f hL d V c k W hW t
    u v hvBoundary a ha N hN⟩

/-- Finitely many full mixed equations have one compatible power multiple. -/
theorem exists_compatible_power (u v : Sections f hL d V c k W hW)
    (hu : ∀ a b : C,
      (MixedFrames.mixedChartFirst a.val.label b.val.label a.val.domain b.val.domain).appTop
        (u a).val =
      (MixedFrames.mixedChartSecond a.val.label b.val.label a.val.domain b.val.domain).appTop
        (u b).val)
    (hv : ∀ a b : C, ∃ N : ℕ,
      ((MixedFrames.mixedChartFirst a.val.label b.val.label a.val.domain b.val.domain).appTop
        (u a).val) ^ N *
          MixedFrames.ChartFamily.difference (fullRelationSchemeEquivalence f hL d V c k)
            (fun j : C ↦ j.val.size) (fun j ↦ j.val.label) (fun j ↦ j.val.domain)
            (fun j ↦ j.val.stable) v a b = 0) :
    ∃ N : ℕ, ∀ a b : C,
      (MixedFrames.mixedChartFirst a.val.label b.val.label a.val.domain b.val.domain).appTop
        ((u a ^ N * v a).val) =
      (MixedFrames.mixedChartSecond a.val.label b.val.label a.val.domain b.val.domain).appTop
        ((u b ^ N * v b).val) :=
  MixedFrames.ChartFamily.exists_compatible_power_mul
    (fullRelationSchemeEquivalence f hL d V c k)
    (fun j : C ↦ j.val.size) (fun j ↦ j.val.label) (fun j ↦ j.val.domain)
    (fun j ↦ j.val.stable) u v hu hv

/-- A compatible scalar and power-torsion discrepancies yield an original lifting multiplier. -/
theorem original_multiplier_of_torsion (u v : Sections f hL d V c k W hW)
    (hvBoundary : ∀ j : C,
      normalizedBoundaryChartMap f hL d V c k j.val.size j.val.label j.val.domain j.val.stable
        (v j) = normalizedOrbitBoundaryCoefficient f hL d V c k j.val.size j.val.label W
          j.val.domain j.val.stable j.val.overDomain t)
    (hu : ∀ a b : C,
      (MixedFrames.mixedChartFirst a.val.label b.val.label a.val.domain b.val.domain).appTop
        (u a).val =
      (MixedFrames.mixedChartSecond a.val.label b.val.label a.val.domain b.val.domain).appTop
        (u b).val)
    (hv : ∀ a b : C, ∃ N : ℕ,
      ((MixedFrames.mixedChartFirst a.val.label b.val.label a.val.domain b.val.domain).appTop
        (u a).val) ^ N *
          MixedFrames.ChartFamily.difference (fullRelationSchemeEquivalence f hL d V c k)
            (fun j : C ↦ j.val.size) (fun j ↦ j.val.label) (fun j ↦ j.val.domain)
            (fun j ↦ j.val.stable) v a b = 0) :
    ∃ a : (invariantSheaf e).obj.obj (op W),
      (∀ j : C, (chartMap f hL d V c k W j.val).appTop
        (orbitFunctions e W a).val = (u j).val) ∧
      ∃ N : ℕ, a ^ N ∈ originalBoundaryLiftIdeal f hL d V c k W t := by
  exact (exists_compatible_power f hL d V c k W hW u v hu hv).elim fun N hN ↦
    (original_multiplier_of_compatible_power f hL d V c k W hW t
      u v hvBoundary hu N hN).elim fun a ha ↦ ⟨a, ha.1, N, ha.2⟩

/-- The descended scalar lies in the radical of the actual original lifting ideal. -/
theorem original_radical_multiplier_of_torsion (u v : Sections f hL d V c k W hW)
    (hvBoundary : ∀ j : C,
      normalizedBoundaryChartMap f hL d V c k j.val.size j.val.label j.val.domain j.val.stable
        (v j) = normalizedOrbitBoundaryCoefficient f hL d V c k j.val.size j.val.label W
          j.val.domain j.val.stable j.val.overDomain t)
    (hu : ∀ a b : C,
      (MixedFrames.mixedChartFirst a.val.label b.val.label a.val.domain b.val.domain).appTop
        (u a).val =
      (MixedFrames.mixedChartSecond a.val.label b.val.label a.val.domain b.val.domain).appTop
        (u b).val)
    (hv : ∀ a b : C, ∃ N : ℕ,
      ((MixedFrames.mixedChartFirst a.val.label b.val.label a.val.domain b.val.domain).appTop
        (u a).val) ^ N *
          MixedFrames.ChartFamily.difference (fullRelationSchemeEquivalence f hL d V c k)
            (fun j : C ↦ j.val.size) (fun j ↦ j.val.label) (fun j ↦ j.val.domain)
            (fun j ↦ j.val.stable) v a b = 0) :
    ∃ a : (invariantSheaf e).obj.obj (op W),
      (∀ j : C, (chartMap f hL d V c k W j.val).appTop
        (orbitFunctions e W a).val = (u j).val) ∧
      a ∈ (originalBoundaryLiftIdeal f hL d V c k W t).radical := by
  obtain ⟨a, ha, N, hN⟩ := original_multiplier_of_torsion f hL d V c k W hW t u v hvBoundary hu hv
  exact ⟨a, ha, Ideal.mem_radical_iff.mpr ⟨N, hN⟩⟩

/-- Simultaneous kernel corrections may be made before clearing torsion discrepancies. -/
theorem original_multiplier_of_corrected_torsion (u correction : Sections f hL d V c k W hW)
    (hz : ∀ j : C,
      normalizedBoundaryChartMap f hL d V c k j.val.size j.val.label j.val.domain j.val.stable
        (correction j) = 0)
    (hu : ∀ a b : C,
      (MixedFrames.mixedChartFirst a.val.label b.val.label a.val.domain b.val.domain).appTop
        (u a).val =
      (MixedFrames.mixedChartSecond a.val.label b.val.label a.val.domain b.val.domain).appTop
        (u b).val)
    (hv : ∀ a b : C, ∃ N : ℕ,
      ((MixedFrames.mixedChartFirst a.val.label b.val.label a.val.domain b.val.domain).appTop
        (u a).val) ^ N *
          MixedFrames.ChartFamily.difference (fullRelationSchemeEquivalence f hL d V c k)
            (fun j : C ↦ j.val.size) (fun j ↦ j.val.label) (fun j ↦ j.val.domain)
            (fun j ↦ j.val.stable) (lifts f hL d V c k W hW t - correction) a b = 0) :
    ∃ a : (invariantSheaf e).obj.obj (op W),
      (∀ j : C, (chartMap f hL d V c k W j.val).appTop
        (orbitFunctions e W a).val = (u j).val) ∧
      ∃ N : ℕ, a ^ N ∈ originalBoundaryLiftIdeal f hL d V c k W t := by
  apply original_multiplier_of_torsion f hL d V c k W hW t u
    (lifts f hL d V c k W hW t - correction) _ hu hv
  intro j
  change normalizedBoundaryChartMap f hL d V c k j.val.size j.val.label
    j.val.domain j.val.stable (lifts f hL d V c k W hW t j - correction j) = _
  rw [map_sub, hz j, sub_zero, lifts_restrict]

end OrbitBoundaryAtlas.FiniteAtlas
end FLT.Mazur.HilbertChart.AffineRestriction
