/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.AuxiliaryLevelHomScheme
public import Mathlib.CategoryTheory.Endomorphism
public import Mathlib.Algebra.Group.End

/-!
# Relabeling the actual marking scheme

Precomposition of marked sections is represented by a scheme morphism.
Automorphisms of the finite label group give an actual finite-group action,
with the inverse convention required for a left action on schemes.
-/

@[expose] public noncomputable section

set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry MonObj

namespace FLT.Mazur.AuxiliaryLevel

variable {S : Scheme} (E : Over S) [GrpObj E]
  {A B C : Type} [Group A] [Group B] [Group C] [Fintype A] [Fintype B] [Fintype C]

/-- Precomposition of markings, as a morphism of the constructed schemes. -/
def relabel (f : B →* A) : homScheme E A ⟶ homScheme E B :=
  liftMarking E B ((universalMarking E A).comp f)

/-- The actual relabeling morphism has the prescribed values. -/
@[reassoc (attr := simp)] theorem relabel_value (f : B →* A) (b : B) :
    relabel E f ≫ value E B b = value E A (f b) :=
  liftMarking_value E B _ b

/-- Identity relabeling is the identity morphism. -/
@[simp] theorem relabel_id : relabel E (MonoidHom.id A) = 𝟙 (homScheme E A) := by
  apply homScheme_ext
  intro a
  simp only [relabel_value, MonoidHom.id_apply, Category.id_comp]

/-- Composed label homomorphisms give composed scheme morphisms in reverse order. -/
theorem relabel_comp (f : B →* A) (g : C →* B) :
    relabel E (f.comp g) = relabel E f ≫ relabel E g := by
  apply homScheme_ext
  intro c
  simp only [relabel_value, MonoidHom.comp_apply, Category.assoc]

/-- A label automorphism yields a scheme automorphism over the original base. -/
def relabelAut (e : MulAut A) : Aut (homScheme E A) where
  hom := relabel E e.symm.toMonoidHom
  inv := relabel E e.toMonoidHom
  hom_inv_id := by
    rw [← relabel_comp]
    have h : e.symm.toMonoidHom.comp e.toMonoidHom = MonoidHom.id A := by
      ext a
      exact e.symm_apply_apply a
    rw [h, relabel_id]
  inv_hom_id := by
    rw [← relabel_comp]
    have h : e.toMonoidHom.comp e.symm.toMonoidHom = MonoidHom.id A := by
      ext a
      exact e.apply_symm_apply a
    rw [h, relabel_id]

/-- The finite automorphism group acts on the actual equation scheme. -/
def relabelAction : MulAut A →* Aut (homScheme E A) where
  toFun := relabelAut E
  map_one' := by
    apply Aut.ext
    exact relabel_id E
  map_mul' e f := by
    apply Aut.ext
    change relabel E (e * f).symm.toMonoidHom =
      relabel E f.symm.toMonoidHom ≫ relabel E e.symm.toMonoidHom
    rw [← relabel_comp]
    rfl

/-- Forgetting the base gives the scheme action required by the quotient construction. -/
def relabelSchemeAction : MulAut A →* Aut (homScheme E A).left :=
  (Functor.mapAut (homScheme E A) (Over.forget S)).comp (relabelAction E)

/-- The action preserves the original structure morphism to the base. -/
@[reassoc (attr := simp)] theorem relabelSchemeAction_base (e : MulAut A) :
    (relabelSchemeAction E e).hom ≫ (homScheme E A).hom = (homScheme E A).hom :=
  (relabelAut E e).hom.w

/-- Relabeling acts by the inverse on the actual universal marked sections. -/
@[reassoc (attr := simp)] theorem relabelAction_value (e : MulAut A) (a : A) :
    (relabelAction E e).hom ≫ value E A a = value E A (e.symm a) :=
  relabel_value E _ _

end FLT.Mazur.AuxiliaryLevel
