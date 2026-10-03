/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.NeronPolygonScaling
public import FLT.Mazur.PolygonActionAssociativity

/-!
# Specializing the polygon action to translations

A smooth-group point specializes the universal action to the existing uniform
scaling followed by cyclic rotation. Both normalization and node formulas hold.
-/

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits MonoidalCategory MonObj
@[expose] public noncomputable section
universe u
namespace FLT.Mazur.PolygonActionTranslation
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
open PolygonPinching PolygonUniversalAction ProjectiveLineActionSpecialization
variable (K : Type u) [Field K]
/-- A unit as a point of the multiplicative group over the base. -/
def gmPoint (a : Kˣ) : 𝟙_ (Over (Spec (.of K))) ⟶ gm K :=
  Over.homMk (unitPoint K a) (unitPoint_base K a)

theorem point_act (a : Kˣ) :
    (λ_ (component K)).inv ≫ gmPoint K a ▷ component K ≫ ProjectiveLineUniversalAction.act K =
      ProjectiveLine.scalingOver K a := by
  apply Over.OverMorphism.ext
  change ((λ_ (component K)).inv.left ≫ (gmPoint K a ▷ component K).left) ≫
    ProjectiveLineUniversalAction.action K = _
  have he : (λ_ (component K)).inv.left ≫ (gmPoint K a ▷ component K).left =
      specialize K a := by
    apply pullback.hom_ext
    · rw [Category.assoc, Over.whiskerRight_left_fst]
      simp only [Over.tensorUnit_hom]
      rw [Over.leftUnitor_inv_left_fst_assoc (component K)]
      exact (pullback.lift_fst _ _ _).symm
    · rw [Category.assoc, Over.whiskerRight_left_snd]
      simp only [Over.tensorUnit_hom]
      rw [Over.leftUnitor_inv_left_snd (component K)]
      exact (pullback.lift_snd _ _ _).symm
  rw [he, specialize_action]
  rfl

variable (n : ℕ) [NeZero n] (hn : 0 < n)
variable {C : Over (Spec (.of K))} (p : components K n ⟶ C) (q : nodes K n ⟶ C)
  (h : IsPushout (toComponents K n hn) (toNodes K n) p q)
/-- A point in a specified component of the split smooth group. -/
def groupPoint (a : Kˣ) (b : ZMod n) : 𝟙_ (Over (Spec (.of K))) ⟶ G K n :=
  gmPoint K a ≫ PolygonSplitGroup.component K n b
/-- Translation obtained by specializing the universal whole-polygon action. -/
def translation (a : Kˣ) (b : ZMod n) : C ⟶ C :=
  (λ_ C).inv ≫ groupPoint K n a b ▷ C ≫ act K n hn p q h
@[reassoc] theorem component_translation (a : Kˣ) (b : ZMod n) (i : Fin n) :
    componentι K n i ≫ p ≫ translation K n hn p q h a b =
      ProjectiveLine.scalingOver K a ≫ componentι K n (rotateIndex b i) ≫ p := by
  rw [translation, ← Category.assoc (componentι K n i) p,
    leftUnitor_inv_naturality_assoc, ← tensorHom_def'_assoc, groupPoint,
    ← whiskerRight_comp_tensorHom_assoc, component_act]
  rw [← Category.assoc (gmPoint K a ▷ component K), ← Category.assoc,
    point_act]

theorem translation_eq (a : Kˣ) (b : ZMod n) : translation K n hn p q h a b =
    polygonScaling K hn p q h a ≫ polygonRotation K hn p q h b := by
  let : Epi p := PolygonActionUnit.normalization_epi K n hn p q h
  apply (cancel_epi p).mp
  apply Sigma.hom_ext
  intro i
  change componentι K n i ≫ p ≫ _ = componentι K n i ≫ p ≫ _
  rw [component_translation]
  simp
@[reassoc] theorem node_translation (a : Kˣ) (b : ZMod n) (i : Fin n) :
    nodeι K n i ≫ q ≫ translation K n hn p q h a b =
      nodeι K n (rotateIndex b i) ≫ q := by
  rw [translation_eq]
  simp
end FLT.Mazur.PolygonActionTranslation
