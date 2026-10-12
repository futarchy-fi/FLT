/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.GrassmannianAmbientGlueData

/-!
# The glued ambient chart scheme over its original base

The coefficient structure maps descend through the proved overlap identifications.
The determinant overlap is the actual scheme intersection of the resulting chart
opens. These statements concern the constructed scheme and do not yet identify
its points with all finite projective ambient quotients.
-/

@[expose] public noncomputable section
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
namespace FLT.Mazur.GrassmannianChart
universe u
variable (R M ι : Type u) [CommRing R] [AddCommGroup M] [Module R M]
  [Fintype ι] (d : ℕ)

/-- The coefficient-base structure morphism descended from all ambient charts. -/
def ambientGrassmannianStructure : ambientGrassmannianScheme R M ι d ⟶ Spec (.of R) :=
  Multicoequalizer.desc (ambientGrassmannianGlueData R M ι d).toGlueData.diagram _
    (fun _ ↦ splitChartStructure R ι d) (by
      rintro ⟨i, j⟩
      change indexedOverlapInclusion i j ≫ splitChartStructure R ι d =
        ((indexedOverlapIso i j).hom ≫ indexedOverlapInclusion j i) ≫ _
      exact (indexedChartTransition_over i j).symm.trans
        (congrArg (fun t ↦ t ≫ splitChartStructure R ι d)
          (indexedOverlapIso_factor i j).symm))

/-- Every glued chart has exactly its original coefficient structure morphism. -/
@[reassoc] theorem ambientGrassmannianChart_over (i : AmbientChartIndex R M ι d) :
    ambientGrassmannianChart R M ι d i ≫ ambientGrassmannianStructure R M ι d =
      splitChartStructure R ι d := by
  unfold ambientGrassmannianChart ambientGrassmannianStructure
  exact Multicoequalizer.π_desc (ambientGrassmannianGlueData R M ι d).toGlueData.diagram
    _ _ _ i

/-- The constructed overlap is the actual intersection of the two glued chart opens. -/
theorem ambientGrassmannianChart_isPullback (i j : AmbientChartIndex R M ι d) :
    IsPullback (indexedOverlapInclusion i j) (indexedChartTransition i j)
      (ambientGrassmannianChart R M ι d i) (ambientGrassmannianChart R M ι d j) := by
  rw [← indexedOverlapIso_factor]
  exact ⟨⟨(ambientGrassmannianGlueData R M ι d).glue_condition i j |>.symm⟩,
    ⟨(ambientGrassmannianGlueData R M ι d).vPullbackConeIsLimit i j⟩⟩

/-- Morphisms from the glued scheme are determined by their restrictions to all ambient charts. -/
theorem ambientGrassmannian_hom_ext {Y : Scheme.{u}}
    (f g : ambientGrassmannianScheme R M ι d ⟶ Y)
    (h : ∀ i, ambientGrassmannianChart R M ι d i ≫ f =
      ambientGrassmannianChart R M ι d i ≫ g) : f = g :=
  Multicoequalizer.hom_ext _ _ _ h

end FLT.Mazur.GrassmannianChart
