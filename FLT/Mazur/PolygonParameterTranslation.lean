/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.GroupActionPointTranslation
public import FLT.Mazur.PolygonActionBaseChange

/-!
# Whole-polygon translations by arbitrary parameter sections

Over any new scheme base, every section of the pulled-back smooth group
acts invertibly on the original pulled-back polygon, including its nodes.
The parameter is not required to descend to a point of the original field.
-/

@[expose] public noncomputable section
open CategoryTheory Limits AlgebraicGeometry MonoidalCategory
open scoped CategoryTheory.Obj
open scoped CategoryTheory.MonObj
namespace FLT.Mazur.PolygonParameterTranslation
open PolygonPinching PolygonUniversalAction PolygonActionBaseChange
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
universe u
variable (K : Type u) [Field K] (n : ℕ) [NeZero n] (hn : 0 < n)
  {C : Over (Spec (.of K))} (p : components K n ⟶ C) (q : nodes K n ⟶ C)
  (h : IsPushout (toComponents K n hn) (toNodes K n) p q)
  {T : Scheme.{u}} (g : T ⟶ Spec (.of K))
local notation "F" => Over.pullback g

/-- The existing base-changed whole-polygon action as a module object. -/
@[instance_reducible] def fullAction : ModObj ((F).obj (G K n)) ((F).obj C) where
  smul := baseChangedAct K n hn p q h g
  one_smul := PolygonActionBaseChange.unit_act K n hn p q h g
  mul_smul := PolygonActionBaseChange.assoc_act K n hn p q h g

/-- Evaluate the whole-polygon action at an arbitrary varying parameter section. -/
def translation (a : 𝟙_ (Over T) ⟶ (F).obj (G K n)) : (F).obj C ⟶ (F).obj C :=
  (λ_ ((F).obj C)).inv ≫ a ▷ (F).obj C ≫ baseChangedAct K n hn p q h g

/-- The original evaluated action has an actual inverse on the whole polygon. -/
def translationIso (a : 𝟙_ (Over T) ⟶ (F).obj (G K n)) : (F).obj C ≅ (F).obj C := by
  let _ := fullAction K n hn p q h g
  exact GroupActionPointTranslation.translationIso a

/-- The automorphism retains the original base-changed action map. -/
theorem translationIso_hom (a : 𝟙_ (Over T) ⟶ (F).obj (G K n)) :
    (translationIso K n hn p q h g a).hom = translation K n hn p q h g a := by
  let _ := fullAction K n hn p q h g
  exact GroupActionPointTranslation.translation_eq a

/-- Varying translations compose by multiplication in the pulled-back group. -/
theorem translation_comp (a b : 𝟙_ (Over T) ⟶ (F).obj (G K n)) :
    translation K n hn p q h g a ≫ translation K n hn p q h g b =
      translation K n hn p q h g (b * a) := by
  let _ := fullAction K n hn p q h g
  have he (c : 𝟙_ (Over T) ⟶ (F).obj (G K n)) :
      GroupActionPointTranslation.translation (X := (F).obj C) c =
        translation K n hn p q h g c := GroupActionPointTranslation.translation_eq c
  rw [← he a, ← he b, ← he (b * a)]
  exact GroupActionPointTranslation.translation_comp a b

/-- The identity section acts as the identity on the entire pulled-back polygon. -/
theorem translation_one : translation K n hn p q h g 1 = 𝟙 ((F).obj C) := by
  let _ := fullAction K n hn p q h g
  have he : GroupActionPointTranslation.translation (X := (F).obj C)
      (1 : 𝟙_ (Over T) ⟶ (F).obj (G K n)) = translation K n hn p q h g 1 :=
    GroupActionPointTranslation.translation_eq 1
  rw [← he]
  exact GroupActionPointTranslation.translation_one

/-- The inverse section is the actual inverse automorphism. -/
theorem translationIso_inv (a : 𝟙_ (Over T) ⟶ (F).obj (G K n)) :
    (translationIso K n hn p q h g a).inv = translation K n hn p q h g a⁻¹ := by
  let _ := fullAction K n hn p q h g
  exact GroupActionPointTranslation.translation_eq a⁻¹

end FLT.Mazur.PolygonParameterTranslation
