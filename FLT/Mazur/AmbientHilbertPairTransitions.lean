/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.AmbientHilbertChartSystem

/-!
# Pairwise transitions for the actual Hilbert atlas

The common ambient chart comparisons give the ordered pair transitions.
Their factorizations on every smaller common open are proved, as are the
identity and inverse laws required by scheme gluing.
-/

@[expose] public noncomputable section

open CategoryTheory AlgebraicGeometry

universe u

namespace FLT.Mazur.HilbertChart.AmbientQuotientCharts

set_option backward.isDefEq.respectTransparency false

variable {R : Type u} [CommRing R] {Z : Scheme.{u}} {z : Z ⟶ Spec (.of R)}
variable (A : AmbientQuotientCharts R z) (d : ℕ)

/-- The open overlap inside the first affine Hilbert chart. -/
def overlap (i j : A.Index) : (A.hilbert d i).Opens := A.support d i (A.common i j)

/-- The actual comparison from the first ordered overlap to the reverse overlap. -/
def transition (i j : A.Index) : (A.overlap d i j).toScheme ≅ (A.overlap d j i).toScheme :=
  A.comparison d i j (A.common i j) inf_le_left inf_le_right ≪≫
    (A.hilbert d j).isoOfEq (congrArg (A.support d j) (inf_comm _ _))

/-- Reordering the common ambient open is itself an actual Hilbert inclusion. -/
theorem transition_hom (i j : A.Index) :
    (A.transition d i j).hom =
      (A.comparison d i j (A.common i j) inf_le_left inf_le_right).hom ≫
        A.inclusion d j (le_of_eq (inf_comm (A.chart i).opensRange (A.chart j).opensRange)) :=
  rfl

/-- On every smaller common open, the transition is the canonical common-open comparison. -/
@[reassoc]
theorem transition_restrict (i j : A.Index) (T : Z.Opens) (h : T ≤ A.common i j) :
    A.inclusion d i h ≫ (A.transition d i j).hom ≫ (A.overlap d j i).ι =
      (A.comparison d i j T (h.trans inf_le_left) (h.trans inf_le_right)).hom ≫
        (A.support d j T).ι := by
  rw [transition_hom]
  simp only [Category.assoc]
  rw [← Category.assoc (A.inclusion d i h),
    A.comparison_restrict d i j (A.common i j) T inf_le_left inf_le_right h]
  simp only [Category.assoc, inclusion, openAmbientHilbertInclusion, overlap, support, common,
    Scheme.homOfLE_ι]

/-- Diagonal overlap support is the entire Hilbert chart. -/
theorem overlap_self (i : A.Index) : A.overlap d i i = ⊤ := A.support_common_self d i

/-- The actual diagonal transition is the identity morphism. -/
theorem transition_self (i : A.Index) : (A.transition d i i).hom = 𝟙 _ := by
  rw [transition_hom, comparison_self, Iso.refl_hom, Category.id_comp]
  exact openAmbientHilbertInclusion_refl ..

/-- Reversing a pair transition gives its inverse, as an equality of actual scheme maps. -/
theorem transition_inverse (i j : A.Index) :
    (A.transition d i j).hom ≫ (A.transition d j i).hom = 𝟙 _ := by
  rw [transition_hom, transition_hom]
  simp only [Category.assoc]
  rw [← Category.assoc (A.inclusion d j _),
    A.comparison_restrict d j i (A.common j i) (A.common i j)
      inf_le_left inf_le_right (le_of_eq (inf_comm _ _))]
  simp only [Category.assoc]
  rw [A.inclusion_comp]
  rw [← Category.assoc, ← Iso.trans_hom,
    A.comparison_trans d i j i (A.common i j) inf_le_left inf_le_right inf_le_left,
    A.comparison_self]
  simp only [Iso.refl_hom]
  exact openAmbientHilbertInclusion_refl ..

end FLT.Mazur.HilbertChart.AmbientQuotientCharts
