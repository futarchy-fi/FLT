/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.AmbientHilbertGluedBase

/-!
# Actual chart intersections and descent for the glued Hilbert scheme

The overlap representatives are the actual intersections of the glued chart
embeddings. Compatible morphisms descend uniquely; these results concern the
constructed scheme and do not assert that the atlas covers every ideal family.
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry

universe u

namespace FLT.Mazur.HilbertChart.AmbientQuotientCharts

set_option backward.isDefEq.respectTransparency false

variable {R : Type u} [CommRing R] {Z : Scheme.{u}} {z : Z ⟶ Spec (.of R)}
variable (A : AmbientQuotientCharts R z) (d : ℕ)

/-- The actual Hilbert chart embeddings agree on their constructed pairwise overlap. -/
@[reassoc]
theorem hilbertChart_overlap (i j : A.Index) :
    (A.transition d i j).hom ≫ (A.overlap d j i).ι ≫ A.hilbertChart d j =
      (A.overlap d i j).ι ≫ A.hilbertChart d i :=
  (A.hilbertGlueData d).glue_condition i j

/-- Each constructed pairwise overlap is the actual intersection in the glued Hilbert scheme. -/
theorem hilbertChart_isPullback (i j : A.Index) :
    IsPullback (A.overlap d i j).ι ((A.transition d i j).hom ≫ (A.overlap d j i).ι)
      (A.hilbertChart d i) (A.hilbertChart d j) where
  w := (A.hilbertChart_overlap d i j).symm.trans (Category.assoc _ _ _).symm
  isLimit' := ⟨(A.hilbertGlueData d).vPullbackConeIsLimit i j⟩

/-- The explicit overlap representative identifies with the actual glued chart pullback. -/
def hilbertChartPullbackIso (i j : A.Index) :
    (A.overlap d i j).toScheme ≅ pullback (A.hilbertChart d i) (A.hilbertChart d j) :=
  (A.hilbertChart_isPullback d i j).isoPullback

variable {Y : Scheme.{u}} (f : ∀ i, A.hilbert d i ⟶ Y)
variable (hf : ∀ i j, (A.transition d i j).hom ≫ (A.overlap d j i).ι ≫ f j =
  (A.overlap d i j).ι ≫ f i)

/-- Compatible morphisms on original affine Hilbert charts descend to the constructed scheme. -/
def hilbertDesc : A.gluedHilbert d ⟶ Y :=
  Multicoequalizer.desc (A.hilbertGlueData d).toGlueData.diagram Y f (by
    rintro ⟨i, j⟩
    exact (hf i j).symm.trans (Category.assoc _ _ _).symm)

/-- The descended morphism has the specified restriction on each original chart. -/
@[reassoc]
theorem hilbertChart_desc (i : A.Index) : A.hilbertChart d i ≫ A.hilbertDesc d f hf = f i :=
  Multicoequalizer.π_desc (A.hilbertGlueData d).toGlueData.diagram Y f _ i

/-- Morphisms out of the glued Hilbert scheme are determined on its actual affine charts. -/
theorem hilbertChart_hom_ext (f g : A.gluedHilbert d ⟶ Y)
    (h : ∀ i, A.hilbertChart d i ≫ f = A.hilbertChart d i ≫ g) : f = g :=
  Multicoequalizer.hom_ext (A.hilbertGlueData d).toGlueData.diagram f g h

end FLT.Mazur.HilbertChart.AmbientQuotientCharts
