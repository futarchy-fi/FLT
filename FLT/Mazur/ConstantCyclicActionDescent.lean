/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.ConstantCyclicSchemeAction

/-!
# Uniqueness and naturality of constant cyclic action descent

An action morphism is determined on the original components. Maps intertwining
the component rotations therefore intertwine the whole scheme action.
-/

@[expose] public noncomputable section
open CategoryTheory Limits AlgebraicGeometry MonoidalCategory
namespace FLT.Mazur.ConstantCyclicSchemeAction
set_option backward.isDefEq.respectTransparency false
variable {S : Scheme} {n : ℕ} [NeZero n] {X Y : Over S}

/-- The descended morphism is uniquely specified by its actual component rotations. -/
theorem act_unique (r : ZMod n → (X ⟶ X))
    (f : ConstantCyclicGroup.model S n ⊗ X ⟶ X)
    (hf : ∀ a, ConstantCyclicGroup.component S n a ▷ X ≫ f = (λ_ X).hom ≫ r a) :
    f = act r := by
  apply FiniteCoproductTensorRight.hom_ext (fun _ : ZMod n ↦ 𝟙_ (Over S))
  intro a
  change ConstantCyclicGroup.component S n a ▷ X ≫ f = _
  rw [component_act, hf]

/-- Intertwining every original rotation intertwines the entire constant group action. -/
theorem act_naturality (r : ZMod n → (X ⟶ X)) (s : ZMod n → (Y ⟶ Y))
    (f : X ⟶ Y) (hf : ∀ a, r a ≫ f = f ≫ s a) :
    act r ≫ f = ConstantCyclicGroup.model S n ◁ f ≫ act s := by
  apply FiniteCoproductTensorRight.hom_ext (fun _ : ZMod n ↦ 𝟙_ (Over S))
  intro a
  change ConstantCyclicGroup.component S n a ▷ X ≫ act r ≫ f = _
  rw [component_act_assoc, ← tensorHom_def_assoc, tensorHom_def'_assoc,
    component_act, leftUnitor_naturality_assoc, hf]

end FLT.Mazur.ConstantCyclicSchemeAction
