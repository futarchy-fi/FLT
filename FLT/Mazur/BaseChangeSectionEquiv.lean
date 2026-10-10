/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import Mathlib.AlgebraicGeometry.PullbackCarrier

/-!
# Sections of an actual base change

Sections of the pullback of a scheme are precisely maps over the original base.
The comparison remembers the original scheme morphism and works over every base.
-/

@[expose] public noncomputable section

set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry

namespace FLT.Mazur.BaseChangeSectionEquiv

universe u
variable {X S T : Scheme.{u}} (f : X ⟶ S) (g : T ⟶ S)

/-- Sections of the actual pullback are the original relative maps. -/
def equiv : {p : T ⟶ pullback f g // p ≫ pullback.snd f g = 𝟙 T} ≃
    (Over.mk g ⟶ Over.mk f) where
  toFun p := Over.homMk (p.val ≫ pullback.fst f g) (by
    change (p.val ≫ pullback.fst f g) ≫ f = g
    rw [Category.assoc, pullback.condition (f := f) (g := g), ← Category.assoc,
      p.property, Category.id_comp])
  invFun p := ⟨pullback.lift p.left (𝟙 T) (by simpa using p.w), by simp⟩
  left_inv p := by
    apply Subtype.ext
    apply pullback.hom_ext
    · simp
    · simpa using p.property.symm
  right_inv p := by
    apply Over.OverMorphism.ext
    simp

/-- The comparison retains the point's projection to the original scheme. -/
theorem equiv_left (p : {p : T ⟶ pullback f g // p ≫ pullback.snd f g = 𝟙 T}) :
    (equiv f g p).left = p.val ≫ pullback.fst f g := rfl

/-- Factoring a relative map through an intermediate base is injective. -/
theorem post_base_injective {U : Scheme.{u}} (h : U ⟶ T) :
    Function.Injective (fun p : Over.mk h ⟶ Over.mk (pullback.snd f g) ↦
      (Over.homMk (p.left ≫ pullback.fst f g) (by
        change (p.left ≫ pullback.fst f g) ≫ f = h ≫ g
        rw [Category.assoc, pullback.condition (f := f) (g := g), ← Category.assoc]
        exact congrArg (fun k ↦ k ≫ g) p.w) :
        Over.mk (h ≫ g) ⟶ Over.mk f)) := by
  intro p q hpq
  apply Over.OverMorphism.ext
  apply pullback.hom_ext
  · exact congrArg (fun p ↦ p.left) hpq
  · exact p.w.trans q.w.symm

end FLT.Mazur.BaseChangeSectionEquiv
