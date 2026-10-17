/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.FiniteGroupPullbackAction

/-!
# Pulling back an equivariant boundary along a moving source

Both maps may move equivariantly over the ambient scheme. The action is built
on their actual pullback, retaining both projections and the closed structure.
-/

@[expose] public noncomputable section
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
namespace FLT.Mazur.FiniteGroupEquivariantPullback
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
variable {G : Type*} [Group G] {X Y Z : Scheme}
  (ρ : G →* Aut X) (τ : G →* Aut Y) (υ : G →* Aut Z)
  (f : X ⟶ Z) (g : Y ⟶ Z)
  (hf : ∀ a, (ρ a).hom ≫ f = f ≫ (υ a).hom)
  (hg : ∀ a, (τ a).hom ≫ g = g ≫ (υ a).hom)

/-- Simultaneous transport of both endpoints in the full fiber product. -/
def map (a : G) : pullback f g ⟶ pullback f g :=
  pullback.lift (pullback.fst f g ≫ (ρ a).hom) (pullback.snd f g ≫ (τ a).hom)
    (by rw [Category.assoc, hf, Category.assoc, hg, pullback.condition_assoc])

/-- The new source projection retains the moving source action. -/
@[reassoc] theorem map_fst (a : G) :
    map ρ τ υ f g hf hg a ≫ pullback.fst f g = pullback.fst f g ≫ (ρ a).hom :=
  pullback.lift_fst _ _ _

/-- The old boundary projection retains the entire original boundary action. -/
@[reassoc] theorem map_snd (a : G) :
    map ρ τ υ f g hf hg a ≫ pullback.snd f g = pullback.snd f g ≫ (τ a).hom :=
  pullback.lift_snd _ _ _

/-- The identity transports neither endpoint. -/
theorem map_one : map ρ τ υ f g hf hg 1 = 𝟙 _ := by
  apply pullback.hom_ext
  · rw [map_fst, _root_.map_one]
    change pullback.fst f g ≫ 𝟙 X = 𝟙 _ ≫ pullback.fst f g
    rw [Category.comp_id, Category.id_comp]
  · rw [map_snd, _root_.map_one]
    change pullback.snd f g ≫ 𝟙 Y = 𝟙 _ ≫ pullback.snd f g
    rw [Category.comp_id, Category.id_comp]

/-- Composition agrees with multiplication of moving permutations. -/
theorem map_mul (a b : G) :
    map ρ τ υ f g hf hg (a * b) =
      map ρ τ υ f g hf hg b ≫ map ρ τ υ f g hf hg a := by
  apply pullback.hom_ext
  · rw [map_fst, Category.assoc, map_fst, map_fst_assoc, _root_.map_mul]
    rfl
  · rw [map_snd, Category.assoc, map_snd, map_snd_assoc, _root_.map_mul]
    rfl

/-- Each simultaneous transport is an automorphism of the actual fiber product. -/
def aut (a : G) : Aut (pullback f g) where
  hom := map ρ τ υ f g hf hg a
  inv := map ρ τ υ f g hf hg a⁻¹
  hom_inv_id := by rw [← map_mul, inv_mul_cancel, map_one]
  inv_hom_id := by rw [← map_mul, mul_inv_cancel, map_one]

/-- The constructed action on the whole equivariant pullback. -/
def action : G →* Aut (pullback f g) where
  toFun := aut ρ τ υ f g hf hg
  map_one' := Aut.ext (map_one ρ τ υ f g hf hg)
  map_mul' a b := Aut.ext (map_mul ρ τ υ f g hf hg a b)

/-- The first projection is equivariant without any reducedness hypothesis. -/
@[reassoc] theorem action_fst (a : G) :
    (action ρ τ υ f g hf hg a).hom ≫ pullback.fst f g =
      pullback.fst f g ≫ (ρ a).hom := map_fst ρ τ υ f g hf hg a

/-- The second projection is equivariant for the original boundary action. -/
@[reassoc] theorem action_snd (a : G) :
    (action ρ τ υ f g hf hg a).hom ≫ pullback.snd f g =
      pullback.snd f g ≫ (τ a).hom := map_snd ρ τ υ f g hf hg a

end FLT.Mazur.FiniteGroupEquivariantPullback
