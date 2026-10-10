/-
Copyright (c) 2026 krandder. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: krandder
-/
module

public import FLT.Mazur.BlowupReesDegreeZeroEquiv
public import Mathlib.AlgebraicGeometry.ProjectiveSpectrum.Basic

/-!
# Actual fraction charts as standard opens of the original Rees Proj

The degree-zero comparison identifies Spec A[I/f] with D₊(f*T) in the
projective spectrum of the original graded Rees algebra. This is a local
identification; compatibility of these maps with the global equation atlas
remains a separate gluing step.
-/

@[expose] public noncomputable section

open AlgebraicGeometry CategoryTheory

namespace FLT.Mazur.BlowupRees

set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true

universe u
variable {A : Type u} [CommRing A] (I : Ideal A) (f : A) (hf : f ∈ I)

/-- The projective spectrum of the original graded Rees algebra. -/
def proj : Scheme := Proj (component I)

/-- The standard Proj open belonging to an original generator of the center. -/
def generatorOpen : (proj I).Opens := Proj.basicOpen (component I) (generator I f hf)

/-- The original fraction chart is the spectrum of the degree-zero Rees localization. -/
def fractionSpecIso : Spec (.of (BlowupFractionChart.chart I f)) ≅
    Spec (.of (DegreeZeroChart I f hf)) :=
  Scheme.Spec.mapIso (degreeZeroEquiv I f hf).toCommRingCatIso.op

/-- The standard open in Rees Proj is the spectrum of the actual fraction algebra. -/
def generatorOpenIso : (generatorOpen I f hf).toScheme ≅
    Spec (.of (BlowupFractionChart.chart I f)) :=
  (Proj.basicOpenIsoSpec (component I) (generator I f hf) (generator_mem I f hf)
    (by decide : 0 < 1)) ≪≫ (fractionSpecIso I f hf).symm

/-- The actual fraction chart maps into the original Rees Proj. -/
def fractionChartInclusion : Spec (.of (BlowupFractionChart.chart I f)) ⟶ proj I :=
  (fractionSpecIso I f hf).hom ≫
    Proj.awayι (component I) (generator I f hf) (generator_mem I f hf) (by decide : 0 < 1)

instance fractionChartInclusion_isOpenImmersion :
    IsOpenImmersion (fractionChartInclusion I f hf) := by
  let _ : IsOpenImmersion (fractionSpecIso I f hf).hom := IsOpenImmersion.of_isIso _
  exact IsOpenImmersion.comp _ _

/-- The fraction chart has exactly the prescribed original generator's standard open as image. -/
theorem fractionChartInclusion_range :
    (fractionChartInclusion I f hf).opensRange = generatorOpen I f hf := by
  exact (Scheme.Hom.opensRange_comp_of_isIso (fractionSpecIso I f hf).hom
    (Proj.awayι (component I) (generator I f hf) (generator_mem I f hf) (by decide))).trans
      (Proj.opensRange_awayι (component I) (generator I f hf) (generator_mem I f hf) (by decide))

/-- The open comparison followed by the fraction inclusion is the original open inclusion. -/
@[reassoc] theorem generatorOpenIso_inclusion :
    (generatorOpenIso I f hf).hom ≫ fractionChartInclusion I f hf =
      (generatorOpen I f hf).ι := by
  simp only [generatorOpenIso, fractionChartInclusion, Iso.trans_hom, Iso.symm_hom,
    Category.assoc, Iso.inv_hom_id_assoc, Proj.awayι, Iso.hom_inv_id_assoc]
  rfl

end FLT.Mazur.BlowupRees
