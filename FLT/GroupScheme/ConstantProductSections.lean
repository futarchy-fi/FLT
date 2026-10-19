/-
Copyright (c) 2026 krandder. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: krandder
-/
module

public import FLT.Mazur.ConstantCyclicGroup

/-!
# Original sections detect maps from a constant group product

The product coproduct cover remains a colimit after forgetting the base.
Thus the component pairs detect arbitrary scheme morphisms, including maps
whose target is over a different base.
-/

@[expose] public noncomputable section

set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false

universe u

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry MonoidalCategory
open CartesianMonoidalCategory

namespace FLT.GroupScheme

/-- Pairs of components detect scheme morphisms out of a product of finite coproducts. -/
theorem coproduct_product_left_hom_ext {S T : Scheme.{u}} {I J : Type} [Finite I] [Finite J]
    (X : I → Over S) (Y : J → Over S)
    {f g : ((∐ X) ⊗ (∐ Y)).left ⟶ T}
    (h : ∀ i j, (Sigma.ι X i ⊗ₘ Sigma.ι Y j).left ≫ f =
      (Sigma.ι X i ⊗ₘ Sigma.ι Y j).left ≫ g) : f = g := by
  apply (isColimitOfPreserves (Over.forget S)
    (FLT.Mazur.PolygonSplitGroup.productCofanIsColimit X Y)).hom_ext
  rintro ⟨i, j⟩
  exact h i j

/-- The original point pairs detect maps from the constant cyclic scheme product. -/
theorem constantCyclic_pair_hom_ext (S T : Scheme.{u}) (n : ℕ) [NeZero n]
    {f g : (FLT.Mazur.ConstantCyclicGroup.model S n ⊗
      FLT.Mazur.ConstantCyclicGroup.model S n).left ⟶ T}
    (h : ∀ i j, (lift (FLT.Mazur.ConstantCyclicGroup.component S n i)
      (FLT.Mazur.ConstantCyclicGroup.component S n j)).left ≫ f =
        (lift (FLT.Mazur.ConstantCyclicGroup.component S n i)
          (FLT.Mazur.ConstantCyclicGroup.component S n j)).left ≫ g) : f = g := by
  apply coproduct_product_left_hom_ext
    (fun _ : ZMod n ↦ 𝟙_ (Over S)) (fun _ : ZMod n ↦ 𝟙_ (Over S))
  intro i j
  apply (cancel_epi (λ_ (𝟙_ (Over S))).inv.left).mp
  have hd : (λ_ (𝟙_ (Over S))).inv = lift (𝟙 _) (𝟙 _) := by
    apply hom_ext <;> simp
  simpa only [← Over.comp_left_assoc, hd, lift_map, Category.id_comp] using h i j

end FLT.GroupScheme
