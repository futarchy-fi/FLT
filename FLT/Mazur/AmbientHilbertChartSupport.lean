/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.AmbientHilbertChartFamilyPullback
public import FLT.Mazur.RelativeIdealSupportRange

/-!
# Support factorization for extended universal chart families

A chart parameter enters a Hilbert support open precisely when its extended
full family lies in that original ambient open. This detects common chart
overlaps using the family in the shared ambient.
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
open FLT.Mazur.ClosedIdealCover

universe u

namespace FLT.Mazur.HilbertChart.AmbientQuotientCharts

set_option backward.isDefEq.respectTransparency false

variable {R : Type u} [CommRing R] {Z : Scheme.{u}} {z : Z ⟶ Spec (.of R)}
variable (A : AmbientQuotientCharts R z) (d : ℕ) [IsSeparated z]
variable {X : Scheme.{u}} (s : X ⟶ Spec (.of R)) (i : A.Index)
variable (p : AmbientSchemeParameters R (A.Vars i) d (A.relations i) s)

/-- The extended family's original ambient range is the original affine family's image. -/
theorem chartParameterFamily_ambientRange :
    Set.range ((A.chartParameterFamily d s i p).val.subschemeι ≫ pullback.snd s z) =
      Set.range (quotientFamilyAmbientMap R (A.Vars i) d (A.relations i) s
        (ambientSchemeClassification R (A.Vars i) d (A.relations i) s p) ≫ A.chart i) := by
  let J := ambientSchemeClassification R (A.Vars i) d (A.relations i) s p
  let m := relativeIdealAmbientHom (A.originalChartBase i) z (A.chart i) (A.chart_over i) s
  calc
    _ = pullback.snd s z '' Set.range (A.chartParameterFamily d s i p).val.subschemeι :=
      Set.range_comp _ _
    _ = pullback.snd s z '' Set.range (J.val.subschemeι ≫ m) := by
      rw [chartParameterFamily, relativeIdealFamilyExtension_range]
    _ = Set.range (J.val.subschemeι ≫ m ≫ pullback.snd s z) := by
      simp only [Scheme.Hom.comp_base, TopCat.coe_comp, Set.range_comp, Set.image_image]
      rfl
    _ = _ := by
      rw [relativeIdealAmbientHom_snd]
      rfl

/-- Every extended chart family stays in its original ambient chart. -/
theorem chartParameterFamily_originalSupport :
    Set.range ((A.chartParameterFamily d s i p).val.subschemeι ≫ pullback.snd s z) ⊆
      (A.chart i).opensRange := by
  rw [A.chartParameterFamily_ambientRange d s i p]
  rintro _ ⟨x, rfl⟩
  exact ⟨_, rfl⟩

/-- Hilbert support factorization is detected by the full family's original ambient map. -/
theorem chartParameterFamily_support_iff (U : Z.Opens) :
    Set.range p.val ⊆ A.support d i U ↔
      Set.range ((A.chartParameterFamily d s i p).val.subschemeι ≫ pullback.snd s z) ⊆ U := by
  rw [chartParameterFamily_ambientRange]
  change Set.range p.val ⊆
    ambientHilbertSupportOpen R (A.Vars i) d (A.relations i) (A.chart i ⁻¹ᵁ U) ↔ _
  rw [range_subset_ambientHilbertSupportOpen_iff]
  simp only [Scheme.Hom.comp_base, TopCat.coe_comp, Set.range_comp, Set.image_subset_iff]
  rfl

end FLT.Mazur.HilbertChart.AmbientQuotientCharts
