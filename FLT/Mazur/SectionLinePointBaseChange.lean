/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.NormalizedSectionLineBaseChange
public import FLT.Mazur.ProjectiveSectionLineChart

/-!
# Naturality of the affine section-line classification

The actual projective point of an extended section submodule is the pullback
of its original point. Consequently the equivalence classifying affine chart
morphisms commutes with changes of the affine test ring in both directions.
-/

@[expose] public noncomputable section
open CategoryTheory AlgebraicGeometry
universe u
namespace FLT.Mazur.ProjectiveSpace
variable (R : Type u) [CommRing R] (ι : Type u)
variable {S T : Type u} [CommRing S] [CommRing T]

/-- The represented scheme point commutes with actual base change of the section submodule. -/
lemma sectionLinePoint_map (g : S →+* T) (f : R →+* S) (i : ι)
    (L : NormalizedSectionLine.Chart S ι i) :
    Spec.map (CommRingCat.ofHom g) ≫ sectionLinePoint R ι f i L =
      sectionLinePoint R ι (g.comp f) i (NormalizedSectionLine.baseChange g i L) := by
  simp only [sectionLinePoint_eq_unitChartPoint, unitChartPoint_map,
    NormalizedSectionLine.generator_baseChange, map_one]

/-- Pull back a genuine affine chart morphism along a map of test rings. -/
def affineChartPointMap (g : S →+* T) (f : R →+* S) (i : ι)
    (p : AffineChartPoint R ι f i) : AffineChartPoint R ι (g.comp f) i :=
  ⟨Spec.map (CommRingCat.ofHom g) ≫ p.val, by
    rw [Category.assoc, p.property, ← Spec.map_comp]
    rfl⟩

/-- Classification commutes with extension of the actual section submodule. -/
lemma sectionLineChartEquiv_map (g : S →+* T) (f : R →+* S) (i : ι)
    (p : AffineChartPoint R ι f i) :
    sectionLineChartEquiv R ι (g.comp f) i (affineChartPointMap R ι g f i p) =
      NormalizedSectionLine.baseChange g i (sectionLineChartEquiv R ι f i p) := by
  apply sectionLinePoint_injective R ι (g.comp f) i
  rw [sectionLinePoint_classify, ← sectionLinePoint_map, sectionLinePoint_classify]
  exact Category.assoc _ _ _

/-- The inverse classification also commutes with pullback of affine chart morphisms. -/
lemma sectionLineChartEquiv_symm_map (g : S →+* T) (f : R →+* S) (i : ι)
    (L : NormalizedSectionLine.Chart S ι i) :
    (sectionLineChartEquiv R ι (g.comp f) i).symm (NormalizedSectionLine.baseChange g i L) =
      affineChartPointMap R ι g f i ((sectionLineChartEquiv R ι f i).symm L) := by
  apply (sectionLineChartEquiv R ι (g.comp f) i).injective
  simp only [Equiv.apply_symm_apply, sectionLineChartEquiv_map]

end FLT.Mazur.ProjectiveSpace
