/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.RelativeCoefficientBaseChange

/-!
# Etale coefficient projections under arbitrary ground changes

Factor through the actual ground pullback of the source. Etaleness of this
relative source comparison suffices; the ground map need not be etale.
-/

@[expose] public noncomputable section
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
namespace FLT.Mazur.RelativeCoefficientBaseChange
set_option backward.isDefEq.respectTransparency false
variable {S S' : Scheme} (a : S' ⟶ S) {A T : Over S} {B : Over S'}

/-- The genuine base change of an old coefficient morphism. -/
def baseMap (w : A ⟶ T) : target a (T := A) ⟶ target a (T := T) :=
  projection a (toOld a) w

@[reassoc]
theorem baseMap_toOld (w : A ⟶ T) :
    (baseMap a w).left ≫ (toOld a).left = (toOld a).left ≫ w.left :=
  congrArg Over.Hom.left (projection_toOld a (toOld a) w)

/-- The coefficient square is Cartesian without any condition on the ground map. -/
theorem baseMap_isPullback (w : A ⟶ T) :
    IsPullback (toOld a).left (baseMap a w).left w.left (toOld a).left := by
  have H : IsPullback (toOld a (T := A)).left (target a (T := A)).hom
      (w.left ≫ T.hom) a := by
    rw [w.w]
    exact IsPullback.of_hasPullback A.hom a
  rw [← (baseMap a w).w] at H
  exact H.of_bot (baseMap_toOld a w).symm (IsPullback.of_hasPullback T.hom a)

instance baseMap_etale (w : A ⟶ T) [Etale w.left] : Etale (baseMap a w).left :=
  MorphismProperty.of_isPullback (baseMap_isPullback a w)
    (inferInstanceAs (Etale w.left))

/-- The relative source map followed by the changed coefficient map is the old projection. -/
theorem projection_factor (u : (Over.map a).obj B ⟶ A) (w : A ⟶ T) :
    projection a u w = projection a u (𝟙 A) ≫ baseMap a w := by
  apply Over.OverMorphism.ext
  apply pullback.hom_ext
  · simp only [projection, baseMap, toOld, Over.homMk_left, Over.comp_left,
      Over.id_left, Category.assoc, pullback.lift_fst, pullback.lift_fst_assoc, Category.comp_id]
  · simp only [projection, baseMap, Over.homMk_left, Over.comp_left,
      Category.assoc, target, Over.pullback_obj_hom, pullback.lift_snd]

/-- Relative etaleness replaces etaleness of the absolute ground and source maps. -/
theorem projection_etale_of_relative (u : (Over.map a).obj B ⟶ A) (w : A ⟶ T)
    [Etale (projection a u (𝟙 A)).left] [Etale w.left] :
    Etale (projection a u w).left := by
  rw [projection_factor]
  exact inferInstanceAs (Etale ((projection a u (𝟙 A)).left ≫ (baseMap a w).left))

end FLT.Mazur.RelativeCoefficientBaseChange
