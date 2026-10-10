/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.AmbientHilbertChartFamilyPullback
public import FLT.Mazur.HilbertIntrinsicContainingExtension

/-!
# Full common-open parameter families in the original ambient

An intrinsic ideal classified on a Hilbert support open extends directly into
the original separated ambient. This equals the extension of the containing
affine family classified by the same parameter, on the level of full ideals.
-/

@[expose] public noncomputable section

open CategoryTheory AlgebraicGeometry
open Scheme.IdealSheafData FLT.Mazur.ClosedIdealCover

universe u

namespace FLT.Mazur.HilbertChart.AmbientQuotientCharts

set_option backward.isDefEq.respectTransparency false

variable {R : Type u} [CommRing R] {Z : Scheme.{u}} {z : Z ⟶ Spec (.of R)}
variable (A : AmbientQuotientCharts R z) (d : ℕ) [IsSeparated z]
variable {X : Scheme.{u}} (s : X ⟶ Spec (.of R))

omit [IsSeparated z] in
/-- The original chart restricted to an ambient open remains over the coefficient scheme. -/
theorem originalOpen_over (i : A.Index) (U : Z.Opens) :
    ((A.chart i ⁻¹ᵁ U).ι ≫ A.chart i) ≫ z =
      quotientOriginalOpenStructure R (A.Vars i) (A.relations i) (A.chart i ⁻¹ᵁ U) := by
  rw [Category.assoc, A.chart_over]
  rfl

/-- The intrinsic common-open family extended into the original separated ambient. -/
def openParameterFamily (i : A.Index) (U : Z.Opens)
    (p : OpenAmbientSchemeParameters R (A.Vars i) d (A.relations i) (A.chart i ⁻¹ᵁ U) s) :
    RelativeIdealFamilies z d s :=
  relativeIdealFamilyExtension
    (quotientOriginalOpenStructure R (A.Vars i) (A.relations i) (A.chart i ⁻¹ᵁ U)) z
    ((A.chart i ⁻¹ᵁ U).ι ≫ A.chart i) (A.originalOpen_over i U) s d
    (openIntrinsicSchemeClassification R (A.Vars i) d (A.relations i) (A.chart i ⁻¹ᵁ U) s p)

/-- Direct common-open extension equals extension of the entire containing affine family. -/
theorem openParameterFamily_containing (i : A.Index) (U : Z.Opens)
    (p : OpenAmbientSchemeParameters R (A.Vars i) d (A.relations i) (A.chart i ⁻¹ᵁ U) s) :
    A.openParameterFamily d s i U p = A.chartParameterFamily d s i
      ⟨p.val ≫ (A.support d i U).ι, (Category.assoc _ _ _).trans p.property⟩ := by
  apply Subtype.ext
  change (openIntrinsicSchemeClassification R (A.Vars i) d (A.relations i)
    (A.chart i ⁻¹ᵁ U) s p).val.map _ = _
  rw [← relativeIdealAmbientHom_comp
    (quotientOriginalOpenStructure R (A.Vars i) (A.relations i) (A.chart i ⁻¹ᵁ U))
    (A.originalChartBase i) z (A.chart i ⁻¹ᵁ U).ι rfl s (A.chart i) (A.chart_over i),
    map_comp, openIntrinsicSchemeClassification_containingExtension]
  rfl

end FLT.Mazur.HilbertChart.AmbientQuotientCharts
