/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.AmbientHilbertCommonFamily

/-!
# Actual pair compatibility of full universal Hilbert chart families

On each ordered gluing overlap, the full universal families from its two
charts have equal pullbacks inside the original separated ambient. This is
the family compatibility for the concrete transitions used by the constructed
scheme gluing datum.
-/

@[expose] public noncomputable section

open CategoryTheory AlgebraicGeometry
open FLT.Mazur.ClosedIdealCover

universe u

namespace FLT.Mazur.HilbertChart.AmbientQuotientCharts

set_option backward.isDefEq.respectTransparency false

variable {R : Type u} [CommRing R] {Z : Scheme.{u}} {z : Z ⟶ Spec (.of R)}
variable (A : AmbientQuotientCharts R z) (d : ℕ) [IsSeparated z]

/-- The two universal full ideals agree over the actual ordered Hilbert gluing overlap. -/
theorem chartUniversalFamily_pair (i j : A.Index) :
    relativeIdealFamilyBaseChange z d (A.chartBase d j)
        ((A.overlap d i j).ι ≫ A.chartBase d i)
        ((A.transition d i j).hom ≫ (A.overlap d j i).ι)
        ((Category.assoc _ _ _).trans (A.transition_over d i j))
        (A.chartUniversalFamily d j) =
      relativeIdealFamilyBaseChange z d (A.chartBase d i)
        ((A.overlap d i j).ι ≫ A.chartBase d i) (A.overlap d i j).ι rfl
        (A.chartUniversalFamily d i) := by
  let s := (A.overlap d i j).ι ≫ A.chartBase d i
  let p : OpenAmbientSchemeParameters R (A.Vars i) d (A.relations i)
      (A.chart i ⁻¹ᵁ A.common i j) s := ⟨𝟙 _, Category.id_comp _⟩
  rw [A.chartUniversalFamily_pullback d s j
    ⟨(A.transition d i j).hom ≫ (A.overlap d j i).ι,
      (Category.assoc _ _ _).trans (A.transition_over d i j)⟩,
    A.chartUniversalFamily_pullback d s i ⟨(A.overlap d i j).ι, rfl⟩]
  have h := A.comparisonParameter_containingFamily d s i j (A.common i j)
    inf_le_left inf_le_right p
  have hp :
      (⟨(A.comparisonParameter d s i j (A.common i j) inf_le_left inf_le_right p).val ≫
          (A.support d j (A.common i j)).ι,
          (Category.assoc _ _ _).trans
            (A.comparisonParameter d s i j (A.common i j) inf_le_left inf_le_right p).property⟩ :
        AmbientSchemeParameters R (A.Vars j) d (A.relations j) s) =
      ⟨(A.transition d i j).hom ≫ (A.overlap d j i).ι,
        (Category.assoc _ _ _).trans (A.transition_over d i j)⟩ := by
    apply Subtype.ext
    simp only [comparisonParameter, p, Category.id_comp, transition, Iso.trans_hom,
      Category.assoc, overlap, common, Scheme.isoOfEq_hom_ι]
  rw [hp] at h
  exact h

end FLT.Mazur.HilbertChart.AmbientQuotientCharts
