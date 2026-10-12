/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.GroupObjectPointTranslation

/-!
# Translation and normalization under cartesian monoidal functors

The actual point translation and normalized automorphism commute with
transport of group objects, including arbitrary scheme base change.
-/

@[expose] public noncomputable section
open CategoryTheory MonoidalCategory CartesianMonoidalCategory
open scoped CategoryTheory.MonObj CategoryTheory.Obj
namespace FLT.Mazur.GroupObjectPointTranslation
universe v u v' u'
variable {C : Type u} [Category.{v} C] [CartesianMonoidalCategory C]
  {D : Type u'} [Category.{v'} D] [CartesianMonoidalCategory D]
  (F : C ⥤ D) [F.Monoidal] {G : C} [GrpObj G]

/-- The transported translation uses the transported point and canonical unit comparison. -/
theorem map_translation (p : 𝟙_ C ⟶ G) :
    F.map (translation p) = translation (Functor.LaxMonoidal.ε F ≫ F.map p) := by
  simp only [translation, Functor.map_mul, Functor.map_comp, F.map_id,
    ← Category.assoc, Functor.Monoidal.toUnit_ε]

/-- Origin normalization commutes with transport of the actual automorphism. -/
theorem map_normalizedIso (e : G ≅ G) :
    F.map (normalizedIso e).hom = (normalizedIso (F.mapIso e)).hom := by
  simp only [normalizedIso, Iso.trans_hom, translationIso, Functor.map_comp,
    map_translation, Functor.map_inv', Functor.map_one, Functor.mapIso_hom,
    GrpObj.comp_inv, ← Category.assoc, MonObj.comp_one]

end FLT.Mazur.GroupObjectPointTranslation
