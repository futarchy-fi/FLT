/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.AmbientHilbertOpenParameterFamily
public import FLT.Mazur.RelativeIdealExtensionIsomorphism

/-!
# Full family agreement on actual common Hilbert opens

The intrinsic overlap comparison extends to equality of full families inside
the original separated ambient. This comparison is constructed from the
original chart embeddings and applies to every test-scheme parameter.
-/

@[expose] public noncomputable section

open CategoryTheory AlgebraicGeometry
open FLT.Mazur.ClosedIdealCover FLT.Mazur.OpenIdealCover

universe u

namespace FLT.Mazur.HilbertChart.AmbientQuotientCharts

set_option backward.isDefEq.respectTransparency false

variable {R : Type u} [CommRing R] {Z : Scheme.{u}} {z : Z ⟶ Spec (.of R)}
variable (A : AmbientQuotientCharts R z) (d : ℕ) [IsSeparated z]
variable {X : Scheme.{u}} (s : X ⟶ Spec (.of R))
variable (i j : A.Index) (U : Z.Opens)
variable (hi : U ≤ (A.chart i).opensRange) (hj : U ≤ (A.chart j).opensRange)
variable (p : OpenAmbientSchemeParameters R (A.Vars i) d (A.relations i) (A.chart i ⁻¹ᵁ U) s)

/-- Canonical overlap transport gives the same full family in the original ambient. -/
theorem openParameterFamily_overlap :
    A.openParameterFamily d s j U
        (openAmbientOverlapParameters R (A.Vars i) (A.Vars j) d
          (A.relations i) (A.relations j) (A.chart i ⁻¹ᵁ U) (A.chart j ⁻¹ᵁ U)
          (commonAmbientOpenIso (A.chart i) (A.chart j) U hi hj)
          (commonAmbientOpenIso_coefficient R (A.Vars i) (A.Vars j)
            (A.relations i) (A.relations j) z (A.chart i) (A.chart j)
            (A.chart_over i) (A.chart_over j) U hi hj) s p) =
      A.openParameterFamily d s i U p := by
  unfold openParameterFamily
  rw [openAmbientOverlapParameters_family]
  apply relativeIdealFamilyExtension_iso
  exact commonAmbientOpenIso_over (A.chart i) (A.chart j) U hi hj

/-- The actual scheme comparison acts by a well-defined parameter map over the coefficient base. -/
def comparisonParameter :
    OpenAmbientSchemeParameters R (A.Vars j) d (A.relations j) (A.chart j ⁻¹ᵁ U) s :=
  ⟨p.val ≫ (A.comparison d i j U hi hj).hom, by
    rw [Category.assoc]
    exact (congrArg (p.val ≫ ·)
      (commonAmbientHilbertIso_over R (A.Vars i) (A.Vars j) d
        (A.relations i) (A.relations j) z (A.chart i) (A.chart j)
        (A.chart_over i) (A.chart_over j) U hi hj)).trans p.property⟩

/-- The scheme-level common-open comparison preserves the full extended family. -/
theorem comparisonParameter_family :
    A.openParameterFamily d s j U (A.comparisonParameter d s i j U hi hj p) =
      A.openParameterFamily d s i U p := by
  have h : A.comparisonParameter d s i j U hi hj p =
      openAmbientOverlapParameters R (A.Vars i) (A.Vars j) d
        (A.relations i) (A.relations j) (A.chart i ⁻¹ᵁ U) (A.chart j ⁻¹ᵁ U)
        (commonAmbientOpenIso (A.chart i) (A.chart j) U hi hj)
        (commonAmbientOpenIso_coefficient R (A.Vars i) (A.Vars j)
          (A.relations i) (A.relations j) z (A.chart i) (A.chart j)
          (A.chart_over i) (A.chart_over j) U hi hj) s p := by
    apply Subtype.ext
    exact (openAmbientOverlapIso_parameters R (A.Vars i) (A.Vars j) d
      (A.relations i) (A.relations j) (A.chart i ⁻¹ᵁ U) (A.chart j ⁻¹ᵁ U)
      (commonAmbientOpenIso (A.chart i) (A.chart j) U hi hj)
      (commonAmbientOpenIso_coefficient R (A.Vars i) (A.Vars j)
        (A.relations i) (A.relations j) z (A.chart i) (A.chart j)
        (A.chart_over i) (A.chart_over j) U hi hj) s p).symm
  rw [h]
  exact A.openParameterFamily_overlap d s i j U hi hj p

/-- Common-open comparison identifies the full containing-affine families in the shared ambient. -/
theorem comparisonParameter_containingFamily :
    A.chartParameterFamily d s j
        ⟨(A.comparisonParameter d s i j U hi hj p).val ≫ (A.support d j U).ι,
          (Category.assoc _ _ _).trans (A.comparisonParameter d s i j U hi hj p).property⟩ =
      A.chartParameterFamily d s i
        ⟨p.val ≫ (A.support d i U).ι, (Category.assoc _ _ _).trans p.property⟩ := by
  rw [← A.openParameterFamily_containing d s j U,
    ← A.openParameterFamily_containing d s i U]
  exact A.comparisonParameter_family d s i j U hi hj p

end FLT.Mazur.HilbertChart.AmbientQuotientCharts
