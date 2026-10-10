/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import Mathlib.AlgebraicGeometry.Pullbacks
public import Mathlib.CategoryTheory.Endomorphism

/-!
# Actual group actions on scheme pullbacks

An invariant scheme morphism induces a genuine group action after any
base change. Both projections retain their expected equivariance and
invariance as scheme morphisms, with group laws proved from the pullback
universal property.
-/

@[expose] public noncomputable section

set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true

open CategoryTheory Limits AlgebraicGeometry

namespace FLT.Mazur.FiniteGroupPullback

universe u
variable {G : Type*} [Group G] {X Q S : Scheme.{u}}
variable (ρ : G →* Aut X) (q : X ⟶ Q) (hq : ∀ g : G, (ρ g).hom ≫ q = q)
variable (f : S ⟶ Q)

/-- The pullback endomorphism obtained from the original action and the identity on the base. -/
def actionHom (g : G) : pullback q f ⟶ pullback q f :=
  pullback.lift (pullback.fst q f ≫ (ρ g).hom) (pullback.snd q f)
    (by rw [Category.assoc, hq, pullback.condition])

/-- The first projection is equivariant for the constructed endomorphism. -/
@[reassoc]
lemma actionHom_fst (g : G) :
    actionHom ρ q hq f g ≫ pullback.fst q f = pullback.fst q f ≫ (ρ g).hom :=
  pullback.lift_fst _ _ _

/-- The second projection is invariant under the constructed endomorphism. -/
@[reassoc]
lemma actionHom_snd (g : G) :
    actionHom ρ q hq f g ≫ pullback.snd q f = pullback.snd q f :=
  pullback.lift_snd _ _ _

/-- The identity group element gives the identity pullback morphism. -/
lemma actionHom_one : actionHom ρ q hq f 1 = 𝟙 _ := by
  apply pullback.hom_ext
  · rw [actionHom_fst, map_one]
    change pullback.fst q f ≫ 𝟙 X = 𝟙 _ ≫ pullback.fst q f
    rw [Category.comp_id, Category.id_comp]
  · rw [actionHom_snd, Category.id_comp]

/-- The constructed pullback morphisms obey the actual action composition law. -/
lemma actionHom_mul (g h : G) :
    actionHom ρ q hq f (g * h) = actionHom ρ q hq f h ≫ actionHom ρ q hq f g := by
  apply pullback.hom_ext
  · rw [actionHom_fst, Category.assoc, actionHom_fst,
      actionHom_fst_assoc, map_mul]
    rfl
  · rw [Category.assoc, actionHom_snd, actionHom_snd, actionHom_snd]

/-- Each pullback action morphism has the actual inverse coming from the inverse group element. -/
def actionAut (g : G) : Aut (pullback q f) where
  hom := actionHom ρ q hq f g
  inv := actionHom ρ q hq f g⁻¹
  hom_inv_id := by rw [← actionHom_mul, inv_mul_cancel, actionHom_one]
  inv_hom_id := by rw [← actionHom_mul, mul_inv_cancel, actionHom_one]

/-- The genuine group action on the actual scheme pullback. -/
def action : G →* Aut (pullback q f) where
  toFun := actionAut ρ q hq f
  map_one' := Aut.ext (actionHom_one ρ q hq f)
  map_mul' g h := Aut.ext (actionHom_mul ρ q hq f g h)

/-- The original-scheme projection intertwines the constructed group actions. -/
@[reassoc]
lemma action_fst (g : G) :
    (action ρ q hq f g).hom ≫ pullback.fst q f = pullback.fst q f ≫ (ρ g).hom :=
  actionHom_fst ρ q hq f g

/-- The new-base projection is invariant under the actual pullback group action. -/
@[reassoc]
lemma action_snd (g : G) :
    (action ρ q hq f g).hom ≫ pullback.snd q f = pullback.snd q f :=
  actionHom_snd ρ q hq f g

end FLT.Mazur.FiniteGroupPullback
