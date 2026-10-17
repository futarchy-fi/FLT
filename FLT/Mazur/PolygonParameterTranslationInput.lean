/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.PolygonParameterTranslation

/-!
# Original action inputs for arbitrary parameter translations

The pre-existing translation uses the full pulled-back parameter section and
the unchanged polygon coordinate. Its projection is the original action on
those two coordinates, over any scheme base.
-/

@[expose] public noncomputable section
open CategoryTheory Limits AlgebraicGeometry MonoidalCategory
open CartesianMonoidalCategory
open scoped CategoryTheory.Obj
namespace FLT.Mazur.PolygonParameterTranslation
open PolygonPinching PolygonUniversalAction PolygonActionBaseChange
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
variable (K : Type) [Field K] (n : ℕ) [NeZero n] (hn : 0 < n)
  {C : Over (Spec (.of K))} (p : components K n ⟶ C) (q : nodes K n ⟶ C)
  (h : IsPushout (toComponents K n hn) (toNodes K n) p q)
  {T : Scheme} (g : T ⟶ Spec (.of K))
local notation "F" => Over.pullback g
local notation "CX" => Functor.obj (Over.pullback g) C
variable (c : 𝟙_ (Over T) ⟶ (Over.pullback g).obj (G K n))

/-- The actual original action input of an arbitrary varying translation. -/
def translationInput : (CX).left ⟶ ((G K n) ⊗ C).left :=
  pullback.lift ((CX).hom ≫ c.left ≫ pullback.fst (G K n).hom g)
    (pullback.fst C.hom g) (by
      have hc : c.left ≫ pullback.snd (G K n).hom g = 𝟙 T := c.w
      rw [Category.assoc, Category.assoc, pullback.condition, ← Category.assoc c.left _ _,
        hc]
      exact pullback.condition.symm)

omit [NeZero n] in
/-- The parameter projection is the entire original varying smooth section. -/
@[reassoc] theorem translationInput_fst :
    translationInput K n g c ≫ (fst (G K n) C).left =
      (CX).hom ≫ c.left ≫ pullback.fst (G K n).hom g :=
  pullback.lift_fst _ _ _

omit [NeZero n] in
/-- The polygon projection is the unchanged full original polygon. -/
@[reassoc] theorem translationInput_snd :
    translationInput K n g c ≫ (snd (G K n) C).left = pullback.fst C.hom g :=
  pullback.lift_snd _ _ _

/-- The existing translated polygon projects by its original whole action on the actual input. -/
@[reassoc] theorem translationIso_hom_projection :
    (translationIso K n hn p q h g c).hom.left ≫ pullback.fst C.hom g =
      translationInput K n g c ≫ (act K n hn p q h).left := by
  rw [translationIso_hom, translation, baseChangedAct]
  simp only [Over.comp_left, Category.assoc, Over.pullback_map_left, pullback.lift_fst]
  have he : (λ_ (CX)).inv.left ≫ (c ▷ (CX)).left ≫
      (Functor.LaxMonoidal.μ (F) (G K n) C).left ≫
        pullback.fst ((G K n) ⊗ C).hom g = translationInput K n g c := by
    apply pullback.hom_ext
    · simp only [Category.assoc]
      rw [Over.μ_pullback_left_fst_fst, Over.whiskerRight_left_fst_assoc]
      erw [Over.leftUnitor_inv_left_fst_assoc (CX)]
      exact (translationInput_fst K n g c).symm
    · simp only [Category.assoc]
      rw [Over.μ_pullback_left_fst_snd, Over.whiskerRight_left_snd_assoc]
      erw [Over.leftUnitor_inv_left_snd_assoc (CX)]
      exact (translationInput_snd K n g c).symm
  simpa only [Category.assoc] using congrArg (· ≫ (act K n hn p q h).left) he

end FLT.Mazur.PolygonParameterTranslation
