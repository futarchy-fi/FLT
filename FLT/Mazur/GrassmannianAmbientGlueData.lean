/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.GrassmannianIndexedTripleOverlap
public import Mathlib.AlgebraicGeometry.Gluing

/-!
# Gluing the ambient Grassmannian charts

The actual principal overlap isomorphisms and restricted triple maps satisfy
scheme gluing. This constructs a scheme with an open cover by all indexed
ambient matrix charts. Coverage of arbitrary projective quotients and the
identification of its functor of points remain separate representation theorems.
-/

@[expose] public noncomputable section
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
namespace FLT.Mazur.GrassmannianChart
universe u
variable {R M ι : Type u} [CommRing R] [AddCommGroup M] [Module R M]
  [Fintype ι] {d : ℕ}

/-- The indexed forward and reverse overlap identifications cancel. -/
@[reassoc] theorem indexedOverlapIso_hom_reverse (i j : AmbientChartIndex R M ι d) :
    (indexedOverlapIso i j).hom ≫ (indexedOverlapIso j i).hom = 𝟙 _ := by
  rw [← indexedOverlapIso_symm i j]
  exact (indexedOverlapIso i j).hom_inv_id

/-- Three cyclic restricted transitions recover the original categorical triple domain. -/
theorem indexedTripleTransition_cyclic (i j k : AmbientChartIndex R M ι d) :
    indexedTripleTransition i j k ≫ indexedTripleTransition j k i ≫
      indexedTripleTransition k i j = 𝟙 _ := by
  apply pullback.hom_ext
  · simp only [Category.assoc, Category.id_comp, indexedTripleTransition_twice_fst,
      indexedTripleTransition_snd_assoc, indexedOverlapIso_hom_reverse, Category.comp_id]
  · simp only [Category.assoc, Category.id_comp, indexedTripleTransition_snd,
      indexedTripleTransition_twice_fst_assoc, indexedOverlapIso_hom_reverse,
      Category.comp_id]

variable (R M ι d)

/-- Actual scheme gluing data for all ambient decompositions of the specified ranks. -/
def ambientGrassmannianGlueData : Scheme.GlueData where
  J := AmbientChartIndex R M ι d
  U := indexedChartScheme
  V := fun ij ↦ indexedOverlapScheme ij.1 ij.2
  f := indexedOverlapInclusion
  t := fun i j ↦ (indexedOverlapIso i j).hom
  t_id := indexedOverlapIso_self
  t' := indexedTripleTransition
  t_fac := indexedTripleTransition_snd
  cocycle := indexedTripleTransition_cyclic
  f_open := fun _ _ ↦ inferInstance

/-- The scheme obtained by gluing the actual ambient matrix charts. -/
def ambientGrassmannianScheme : Scheme.{u} := (ambientGrassmannianGlueData R M ι d).glued

/-- Each indexed matrix chart maps to the constructed glued scheme. -/
def ambientGrassmannianChart (i : AmbientChartIndex R M ι d) :
    indexedChartScheme i ⟶ ambientGrassmannianScheme R M ι d :=
  (ambientGrassmannianGlueData R M ι d).ι i

instance (i : AmbientChartIndex R M ι d) :
    IsOpenImmersion (ambientGrassmannianChart R M ι d i) :=
  Scheme.GlueData.ι_isOpenImmersion (ambientGrassmannianGlueData R M ι d) i

/-- The constructed chart maps cover the glued scheme. -/
theorem ambientGrassmannianChart_cover (x : ambientGrassmannianScheme R M ι d) :
    ∃ (i : AmbientChartIndex R M ι d) (y : indexedChartScheme i),
      ambientGrassmannianChart R M ι d i y = x :=
  (ambientGrassmannianGlueData R M ι d).ι_jointly_surjective x

/-- The chart maps agree along exactly the constructed rational overlap transitions. -/
@[reassoc] theorem ambientGrassmannianChart_overlap (i j : AmbientChartIndex R M ι d) :
    indexedChartTransition i j ≫ ambientGrassmannianChart R M ι d j =
      indexedOverlapInclusion i j ≫ ambientGrassmannianChart R M ι d i := by
  rw [← indexedOverlapIso_factor, Category.assoc]
  exact (ambientGrassmannianGlueData R M ι d).glue_condition i j

end FLT.Mazur.GrassmannianChart
