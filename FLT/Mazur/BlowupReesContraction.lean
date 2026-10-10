/-
Copyright (c) 2026 krandder. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: krandder
-/
module

public import FLT.Mazur.BlowupReesZeroComponent

/-!
# The canonical original contraction of Rees Proj

The canonical Proj-to-degree-zero map, followed by the proved identification
with the original coordinate ring, restricts to the actual algebra map on
every fraction chart.
-/

@[expose] public noncomputable section

open AlgebraicGeometry CategoryTheory

namespace FLT.Mazur.BlowupRees

set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true

universe u
variable {A : Type u} [CommRing A] (I : Ideal A)

/-- The canonical Proj contraction to the spectrum of the original coordinate ring. -/
def contraction : proj I ⟶ Spec (.of A) :=
  Proj.toSpecZero (component I) ≫ Spec.map (CommRingCat.ofHom (originalToZero I))

/-- On every actual fraction chart the canonical contraction is the original algebra map. -/
@[reassoc] theorem fractionChartInclusion_contraction (f : A) (hf : f ∈ I) :
    fractionChartInclusion I f hf ≫ contraction I =
      Spec.map (CommRingCat.ofHom (algebraMap A (BlowupFractionChart.chart I f))) := by
  rw [fractionChartInclusion, contraction, Category.assoc, Proj.awayι_toSpecZero_assoc]
  change Spec.map _ ≫ Spec.map _ ≫ Spec.map _ = Spec.map _
  rw [← Spec.map_comp, ← Spec.map_comp]
  congr 1
  apply CommRingCat.hom_ext
  apply RingHom.ext
  intro z
  exact degreeZeroEquiv_original I f hf z

end FLT.Mazur.BlowupRees
