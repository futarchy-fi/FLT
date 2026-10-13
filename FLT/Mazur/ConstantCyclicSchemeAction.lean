/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.FiniteCoproductTensorRight
public import FLT.Mazur.ConstantCyclicGroup

/-!
# A constant cyclic group scheme acts by prescribed rotations

Finite coproduct descent turns a cyclic family of scheme automorphisms into
an actual action morphism on the whole scheme. All action laws are checked
on the original components, with no pointwise density assumption.
-/

@[expose] public noncomputable section
open CategoryTheory Limits AlgebraicGeometry MonoidalCategory MonObj
namespace FLT.Mazur.ConstantCyclicSchemeAction
set_option backward.isDefEq.respectTransparency false
variable {S : Scheme} {n : ℕ} [NeZero n] {X : Over S}
  (r : ZMod n → (X ⟶ X))

/-- The actual action map on the entire scheme, descended from its rotations. -/
def act : ConstantCyclicGroup.model S n ⊗ X ⟶ X :=
  FiniteCoproductTensorRight.desc (fun _ : ZMod n ↦ 𝟙_ (Over S)) X
    (fun a ↦ (λ_ X).hom ≫ r a)

/-- Every original group component acts by its specified scheme rotation. -/
@[reassoc] theorem component_act (a : ZMod n) :
    ConstantCyclicGroup.component S n a ▷ X ≫ act r = (λ_ X).hom ≫ r a :=
  FiniteCoproductTensorRight.component_desc _ _ _ _

/-- Identity rotation supplies the group scheme action's unit law. -/
theorem unit_act (hzero : r 0 = 𝟙 X) :
    η[ConstantCyclicGroup.model S n] ▷ X ≫ act r = (λ_ X).hom := by
  change (η[𝟙_ (Over S)] ≫ ConstantCyclicGroup.component S n 0) ▷ X ≫ _ = _
  rw [comp_whiskerRight, Category.assoc, component_act, hzero, Category.comp_id]
  have he : η[𝟙_ (Over S)] = 𝟙 _ := Subsingleton.elim _ _
  rw [he, id_whiskerRight, Category.id_comp]

/-- Addition of the prescribed rotations supplies the action's associativity law. -/
theorem assoc_act (hadd : ∀ a b, r (a + b) = r a ≫ r b) :
    μ[ConstantCyclicGroup.model S n] ▷ X ≫ act r =
      (α_ (ConstantCyclicGroup.model S n) (ConstantCyclicGroup.model S n) X).hom ≫
        ConstantCyclicGroup.model S n ◁ act r ≫ act r := by
  change ConstantCyclicGroup.multiplication S n ▷ X ≫ act r = _
  apply FiniteCoproductTensorRight.triple_hom_ext
    (fun _ : ZMod n ↦ 𝟙_ (Over S)) (fun _ : ZMod n ↦ 𝟙_ (Over S)) X
  intro a b
  change (ConstantCyclicGroup.component S n a ⊗ₘ
    ConstantCyclicGroup.component S n b) ▷ X ≫ _ = _
  rw [← comp_whiskerRight_assoc, ConstantCyclicGroup.component_multiplication,
    comp_whiskerRight_assoc, component_act]
  rw [← tensorHom_id (ConstantCyclicGroup.component S n a ⊗ₘ
    ConstantCyclicGroup.component S n b) X, associator_naturality_assoc,
    tensorHom_id, tensorHom_comp_whiskerLeft_assoc,
    component_act, ← whiskerLeft_comp_tensorHom_assoc, tensorHom_def'_assoc, component_act]
  rw [leftUnitor_naturality_assoc]
  rw [add_comm a b, hadd]
  have hu : μ[𝟙_ (Over S)] ▷ X ≫ (λ_ X).hom =
      (α_ (𝟙_ (Over S)) (𝟙_ (Over S)) X).hom ≫
        (𝟙_ (Over S)) ◁ (λ_ X).hom ≫ (λ_ X).hom := by
    change (λ_ (𝟙_ (Over S))).hom ▷ X ≫ (λ_ X).hom = _
    rw [← Category.assoc, triangle]
    have he : (λ_ (𝟙_ (Over S))).hom = (ρ_ (𝟙_ (Over S))).hom :=
      Subsingleton.elim _ _
    rw [he]
  simpa only [Category.assoc] using congrArg (fun f ↦ f ≫ r b ≫ r a) hu

/-- An orbit of sections gives an equivariant map from the actual regular action. -/
theorem marking_equivariant (t : ZMod n → (𝟙_ (Over S) ⟶ X))
    (ht : ∀ a b, t b ≫ r a = t (a + b)) :
    μ[ConstantCyclicGroup.model S n] ≫ Sigma.desc t =
      ConstantCyclicGroup.model S n ◁ Sigma.desc t ≫ act r := by
  change ConstantCyclicGroup.multiplication S n ≫ Sigma.desc t = _
  apply PolygonSplitGroup.tensor_hom_ext
    (fun _ : ZMod n ↦ 𝟙_ (Over S)) (fun _ : ZMod n ↦ 𝟙_ (Over S))
  intro a b
  change (ConstantCyclicGroup.component S n a ⊗ₘ
    ConstantCyclicGroup.component S n b) ≫ _ = _
  rw [ConstantCyclicGroup.component_multiplication_assoc, Sigma.ι_comp_desc,
    tensorHom_comp_whiskerLeft_assoc, Sigma.ι_comp_desc,
    tensorHom_def'_assoc, component_act, leftUnitor_naturality_assoc, ht]
  rfl

end FLT.Mazur.ConstantCyclicSchemeAction
