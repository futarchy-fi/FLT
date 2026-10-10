/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import Mathlib.AlgebraicGeometry.Gluing

/-!
# Maps between glued schemes from compatible charts

Chart and overlap maps with their two commuting squares induce a global
map. The chart restrictions determine it and prove identity and composition.
-/

@[expose] public noncomputable section

open CategoryTheory Limits AlgebraicGeometry

namespace FLT.Mazur

universe u

variable (D E : Scheme.GlueData.{u}) (c : E.J → D.J)
  (f : ∀ i, E.U i ⟶ D.U (c i))
  (g : ∀ i j, E.V (i, j) ⟶ D.V (c i, c j))
  (hf : ∀ i j, g i j ≫ D.f (c i) (c j) = E.f i j ≫ f i)
  (ht : ∀ i j, g i j ≫ D.t (c i) (c j) = E.t i j ≫ g j i)

include hf ht in
/-- Compatibility on both overlap arrows makes the chart maps glue. -/
theorem schemeGlueDataMap_compatible (i j : E.J) :
    E.f i j ≫ f i ≫ D.ι (c i) = E.t i j ≫ E.f j i ≫ f j ≫ D.ι (c j) := by
  calc
    _ = g i j ≫ D.f (c i) (c j) ≫ D.ι (c i) := by
      rw [← Category.assoc, ← hf, Category.assoc]
    _ = g i j ≫ D.t (c i) (c j) ≫ D.f (c j) (c i) ≫ D.ι (c j) := by
      rw [D.toGlueData.glue_condition]
    _ = E.t i j ≫ g j i ≫ D.f (c j) (c i) ≫ D.ι (c j) := by
      rw [← Category.assoc (g i j), ht, Category.assoc]
    _ = _ := by rw [← Category.assoc (g j i), hf, Category.assoc]

/-- The global map specified by the compatible chart maps. -/
def schemeGlueDataMap : E.glued ⟶ D.glued :=
  Multicoequalizer.desc E.toGlueData.diagram D.glued (fun i ↦ f i ≫ D.ι (c i))
    (by
      rintro ⟨i, j⟩
      change E.f i j ≫ (f i ≫ D.ι (c i)) =
        (E.t i j ≫ E.f j i) ≫ (f j ≫ D.ι (c j))
      simpa only [Category.assoc] using schemeGlueDataMap_compatible D E c f g hf ht i j)

/-- The induced map has the prescribed restriction on every chart. -/
@[reassoc] theorem schemeGlueDataMap_chart (i : E.J) :
    E.ι i ≫ schemeGlueDataMap D E c f g hf ht = f i ≫ D.ι (c i) :=
  Multicoequalizer.π_desc E.toGlueData.diagram D.glued (fun j ↦ f j ≫ D.ι (c j)) _ i

/-- The chart restrictions determine a morphism out of the glued scheme. -/
theorem schemeGlueData_hom_ext {T : Scheme.{u}} (q r : E.glued ⟶ T)
    (h : ∀ i, E.ι i ≫ q = E.ι i ≫ r) : q = r :=
  Multicoequalizer.hom_ext _ q r h

/-- Identity chart maps induce the identity global map. -/
theorem schemeGlueDataMap_id :
    schemeGlueDataMap D D id (fun _ ↦ 𝟙 _) (fun _ _ ↦ 𝟙 _)
      (fun _ _ ↦ by simp) (fun _ _ ↦ by simp) = 𝟙 D.glued := by
  apply schemeGlueData_hom_ext D
  intro i
  rw [schemeGlueDataMap_chart, Category.id_comp, Category.comp_id]
  rfl

variable (F : Scheme.GlueData.{u}) (d : F.J → E.J)
  (f' : ∀ i, F.U i ⟶ E.U (d i))
  (g' : ∀ i j, F.V (i, j) ⟶ E.V (d i, d j))
  (hf' : ∀ i j, g' i j ≫ E.f (d i) (d j) = F.f i j ≫ f' i)
  (ht' : ∀ i j, g' i j ≫ E.t (d i) (d j) = F.t i j ≫ g' j i)

/-- Composing the chart restrictions determines the composite of global maps. -/
@[reassoc] theorem schemeGlueDataMap_comp_chart (i : F.J) :
    F.ι i ≫ schemeGlueDataMap E F d f' g' hf' ht' ≫
        schemeGlueDataMap D E c f g hf ht =
      f' i ≫ f (d i) ≫ D.ι (c (d i)) := by
  rw [schemeGlueDataMap_chart_assoc, schemeGlueDataMap_chart]

end FLT.Mazur
