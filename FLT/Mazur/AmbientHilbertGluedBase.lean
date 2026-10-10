/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.AmbientHilbertGluing

/-!
# The coefficient-base morphism of the glued Hilbert scheme

The actual pair transitions preserve coefficient structures. The universal
property of scheme gluing therefore constructs the base morphism and proves
that every original affine Hilbert chart lies over the coefficient scheme.
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry

universe u

namespace FLT.Mazur.HilbertChart.AmbientQuotientCharts

set_option backward.isDefEq.respectTransparency false

variable {R : Type u} [CommRing R] {Z : Scheme.{u}} {z : Z ⟶ Spec (.of R)}
variable (A : AmbientQuotientCharts R z) (d : ℕ)

/-- Each affine Hilbert scheme has its original coefficient-base structure. -/
abbrev chartBase (i : A.Index) : A.hilbert d i ⟶ Spec (.of R) :=
  ambientHilbertStructure R (A.Vars i) d (A.relations i)

/-- Common-open Hilbert comparison preserves the coefficient-base structure. -/
@[reassoc]
theorem comparison_over (i j : A.Index) (U : Z.Opens)
    (hi : U ≤ (A.chart i).opensRange) (hj : U ≤ (A.chart j).opensRange) :
    (A.comparison d i j U hi hj).hom ≫ (A.support d j U).ι ≫ A.chartBase d j =
      (A.support d i U).ι ≫ A.chartBase d i := commonAmbientHilbertIso_over ..

/-- Ordered pair transitions preserve the coefficient structures of the affine Hilbert charts. -/
@[reassoc]
theorem transition_over (i j : A.Index) :
    (A.transition d i j).hom ≫ (A.overlap d j i).ι ≫ A.chartBase d j =
      (A.overlap d i j).ι ≫ A.chartBase d i := by
  simp only [transition, Iso.trans_hom, overlap, common, Category.assoc,
    Scheme.isoOfEq_hom_ι_assoc]
  exact A.comparison_over d i j (A.common i j) inf_le_left inf_le_right

/-- The constructed glued Hilbert scheme is an actual scheme over the coefficient base. -/
def gluedBase : A.gluedHilbert d ⟶ Spec (.of R) :=
  Multicoequalizer.desc (A.hilbertGlueData d).toGlueData.diagram (Spec (.of R))
    (A.chartBase d) (by
      rintro ⟨i, j⟩
      exact (A.transition_over d i j).symm.trans (Category.assoc _ _ _).symm)

/-- Every original affine Hilbert chart lies over the constructed base morphism. -/
@[reassoc (attr := simp)]
theorem hilbertChart_over (i : A.Index) :
    A.hilbertChart d i ≫ A.gluedBase d = A.chartBase d i :=
  Multicoequalizer.π_desc (A.hilbertGlueData d).toGlueData.diagram
    (Spec (.of R)) (A.chartBase d) _ i

end FLT.Mazur.HilbertChart.AmbientQuotientCharts
