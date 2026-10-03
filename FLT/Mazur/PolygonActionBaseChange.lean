/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.PolygonActionAssociativity

/-!
# Action laws after arbitrary base change

The tensor comparison of the actual pullback functor transports the polygon
action. Monoidal naturality and coherence preserve its unit and associativity.
-/

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits MonoidalCategory MonObj
@[expose] public noncomputable section
universe u v w z
namespace FLT.Mazur.MonoidalActionMap
variable {D : Type u} [Category.{v} D] [MonoidalCategory D]
  {E : Type w} [Category.{z} E] [MonoidalCategory E]
  (F : D ⥤ E) [F.LaxMonoidal] {G X : D} [MonObj G] (a : G ⊗ X ⟶ X)
open Functor.LaxMonoidal

theorem map_unit (h : η[G] ▷ X ≫ a = (λ_ X).hom) :
    (ε F ≫ F.map η[G]) ▷ F.obj X ≫ Functor.LaxMonoidal.μ F G X ≫ F.map a =
      (λ_ (F.obj X)).hom := by
  simp [comp_whiskerRight, ← F.map_comp, h]

theorem map_assoc
    (h : MonObj.mul (X := G) ▷ X ≫ a = (α_ G G X).hom ≫ G ◁ a ≫ a) :
    (Functor.LaxMonoidal.μ F G G ≫ F.map MonObj.mul) ▷ F.obj X ≫
      Functor.LaxMonoidal.μ F G X ≫ F.map a =
      (α_ (F.obj G) (F.obj G) (F.obj X)).hom ≫
        F.obj G ◁ (Functor.LaxMonoidal.μ F G X ≫ F.map a) ≫
          Functor.LaxMonoidal.μ F G X ≫ F.map a := by
  simp_rw [comp_whiskerRight, Category.assoc, μ_natural_left_assoc,
    MonoidalCategory.whiskerLeft_comp, Category.assoc, μ_natural_right_assoc]
  slice_lhs 3 4 => rw [← F.map_comp, h]
  simp
end FLT.Mazur.MonoidalActionMap

namespace FLT.Mazur.PolygonActionBaseChange
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
open PolygonPinching PolygonUniversalAction
variable (K : Type u) [Field K] (n : ℕ) [NeZero n] (hn : 0 < n)
variable {C : Over (Spec (.of K))} (p : components K n ⟶ C) (q : nodes K n ⟶ C)
  (h : IsPushout (toComponents K n hn) (toNodes K n) p q)
variable {T : Scheme.{u}} (g : T ⟶ Spec (.of K))
open scoped CategoryTheory.Obj
/-- The action pulled back along an arbitrary scheme morphism. -/
def baseChangedAct : (Over.pullback g).obj (G K n) ⊗ (Over.pullback g).obj C ⟶
    (Over.pullback g).obj C :=
  Functor.LaxMonoidal.μ (Over.pullback g) (G K n) C ≫
    (Over.pullback g).map (act K n hn p q h)

theorem unit_act : η[(Over.pullback g).obj (G K n)] ▷ (Over.pullback g).obj C ≫
    baseChangedAct K n hn p q h g = (λ_ ((Over.pullback g).obj C)).hom :=
  MonoidalActionMap.map_unit (Over.pullback g) (act K n hn p q h)
    (PolygonActionUnit.unit_act K n hn p q h)

theorem assoc_act : μ[(Over.pullback g).obj (G K n)] ▷ (Over.pullback g).obj C ≫
    baseChangedAct K n hn p q h g =
    (α_ ((Over.pullback g).obj (G K n)) ((Over.pullback g).obj (G K n))
      ((Over.pullback g).obj C)).hom ≫
    (Over.pullback g).obj (G K n) ◁ baseChangedAct K n hn p q h g ≫
      baseChangedAct K n hn p q h g :=
  MonoidalActionMap.map_assoc (Over.pullback g) (act K n hn p q h)
    (PolygonActionAssociativity.assoc_act K n hn p q h)
end FLT.Mazur.PolygonActionBaseChange
