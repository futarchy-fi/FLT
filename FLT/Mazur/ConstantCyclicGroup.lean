/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.PolygonSplitGroup

/-!
# The constant cyclic group over a scheme

The coproduct of copies of the base indexed by `ZMod n` is a commutative group
scheme. Its operations add and negate component indices, with the unit group
on each component. All group laws are proved on products of those components.
-/

open CategoryTheory Limits AlgebraicGeometry MonObj MonoidalCategory CartesianMonoidalCategory
@[expose] public noncomputable section
universe u
namespace FLT.Mazur.ConstantCyclicGroup
open PolygonSplitGroup (productCofanIsColimit tensor_hom_ext triple_hom_ext)
variable (S : Scheme.{u}) (n : ℕ) [NeZero n]

/-- The constant cyclic group scheme with n components. -/
abbrev model : Over (S) :=
  ∐ fun _ : ZMod n ↦ 𝟙_ (Over S)

/-- Inclusion of one copy of the base scheme. -/
abbrev component (i : ZMod n) : 𝟙_ (Over S) ⟶ model S n :=
  Sigma.ι (fun _ : ZMod n ↦ 𝟙_ (Over S)) i

/-- Multiply in the unit group and add the component indices. -/
def multiplication : model S n ⊗ model S n ⟶ model S n :=
  (productCofanIsColimit (fun _ : ZMod n ↦ 𝟙_ (Over S))
    (fun _ : ZMod n ↦ 𝟙_ (Over S))).desc
      (Cofan.mk _ fun p ↦ μ[𝟙_ (Over S)] ≫ component S n (p.1 + p.2))

@[reassoc (attr := simp)]
theorem component_multiplication (i j : ZMod n) :
    (component S n i ⊗ₘ component S n j) ≫ multiplication S n =
      μ[𝟙_ (Over S)] ≫ component S n (i + j) :=
  (productCofanIsColimit (fun _ : ZMod n ↦ 𝟙_ (Over S))
    (fun _ : ZMod n ↦ 𝟙_ (Over S))).fac _ ⟨i, j⟩

@[reassoc (attr := simp)]
theorem lift_component_multiplication {Z : Over (S)}
    (f g : Z ⟶ 𝟙_ (Over S)) (i j : ZMod n) :
    lift (f ≫ component S n i) (g ≫ component S n j) ≫ multiplication S n =
      lift f g ≫ μ[𝟙_ (Over S)] ≫ component S n (i + j) := by
  rw [← lift_map_assoc, component_multiplication]

/-- The identity lies in component zero. -/
def identity : 𝟙_ (Over (S)) ⟶ model S n :=
  η[𝟙_ (Over S)] ≫ component S n 0

/-- Invert in the unit group and negate the component index. -/
def inversion : model S n ⟶ model S n :=
  Sigma.desc fun i ↦ ι[𝟙_ (Over S)] ≫ component S n (-i)

omit [NeZero n] in
@[reassoc (attr := simp)]
theorem component_inversion (i : ZMod n) :
    component S n i ≫ inversion S n =
      ι[𝟙_ (Over S)] ≫ component S n (-i) := by
  simp [component, inversion]

theorem identity_mul : identity S n ▷ model S n ≫ multiplication S n =
    (λ_ (model S n)).hom := by
  apply (cancel_epi (λ_ (model S n)).inv).mp
  apply Sigma.hom_ext
  intro i
  simp only [Iso.inv_hom_id, Category.comp_id]
  rw [leftUnitor_inv_naturality_assoc]
  rw [← tensorHom_def'_assoc, identity, ← whiskerRight_comp_tensorHom_assoc,
    component_multiplication]
  simp only [zero_add, ← Category.assoc, MonObj.one_mul, Iso.inv_hom_id, Category.id_comp]

theorem mul_identity : model S n ◁ identity S n ≫ multiplication S n =
    (ρ_ (model S n)).hom := by
  apply (cancel_epi (ρ_ (model S n)).inv).mp
  apply Sigma.hom_ext
  intro i
  simp only [Iso.inv_hom_id, Category.comp_id]
  rw [rightUnitor_inv_naturality_assoc]
  rw [← tensorHom_def_assoc, identity, ← whiskerLeft_comp_tensorHom_assoc,
    component_multiplication]
  simp only [add_zero, ← Category.assoc, MonObj.mul_one, Iso.inv_hom_id, Category.id_comp]

theorem multiplication_assoc :
    multiplication S n ▷ model S n ≫ multiplication S n =
      (α_ (model S n) (model S n) (model S n)).hom ≫
        model S n ◁ multiplication S n ≫ multiplication S n := by
  apply triple_hom_ext (fun _ : ZMod n ↦ 𝟙_ (Over S))
    (fun _ : ZMod n ↦ 𝟙_ (Over S))
    (fun _ : ZMod n ↦ 𝟙_ (Over S))
  intro i j k
  rw [tensorHom_comp_whiskerRight_assoc, component_multiplication,
    ← whiskerRight_comp_tensorHom_assoc, component_multiplication]
  rw [associator_naturality_assoc, tensorHom_comp_whiskerLeft_assoc,
    component_multiplication, ← whiskerLeft_comp_tensorHom_assoc, component_multiplication]
  simp only [← Category.assoc, MonObj.mul_assoc, add_assoc]

instance monObj : MonObj (model S n) where
  one := identity S n
  mul := multiplication S n
  one_mul := identity_mul S n
  mul_one := mul_identity S n
  mul_assoc := multiplication_assoc S n

instance grpObj : GrpObj (model S n) where
  inv := inversion S n
  left_inv := by
    change lift (inversion S n) (𝟙 _) ≫ multiplication S n = toUnit _ ≫ identity S n
    apply Sigma.hom_ext
    intro i
    change component S n i ≫ _ = component S n i ≫ _
    rw [comp_lift_assoc, component_inversion, Category.comp_id]
    rw [← Category.id_comp (component S n i), lift_component_multiplication]
    simp only [neg_add_cancel, GrpObj.left_inv_assoc, identity, Category.id_comp, comp_toUnit_assoc]
  right_inv := by
    change lift (𝟙 _) (inversion S n) ≫ multiplication S n = toUnit _ ≫ identity S n
    apply Sigma.hom_ext
    intro i
    change component S n i ≫ _ = component S n i ≫ _
    rw [comp_lift_assoc, component_inversion, Category.comp_id]
    rw [← Category.id_comp (component S n i), lift_component_multiplication]
    simp only [add_neg_cancel, GrpObj.right_inv_assoc, identity, Category.id_comp,
      comp_toUnit_assoc]

instance commGrpObj : CommGrpObj (model S n) where
  mul_comm := by
    change (β_ (model S n) (model S n)).hom ≫ multiplication S n = multiplication S n
    apply tensor_hom_ext (fun _ : ZMod n ↦ 𝟙_ (Over S))
      (fun _ : ZMod n ↦ 𝟙_ (Over S))
    intro i j
    rw [BraidedCategory.braiding_naturality_assoc, component_multiplication,
      component_multiplication,
      IsCommMonObj.mul_comm_assoc, add_comm]


end FLT.Mazur.ConstantCyclicGroup
