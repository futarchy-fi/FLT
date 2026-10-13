/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.PolygonSplitGroup

/-!
# Maps from finite coproducts tensored with an arbitrary scheme

The product coproduct theorem with a singleton second index gives descent and
extensionality for a finite coproduct tensored with a whole scheme over the base.
-/

@[expose] public noncomputable section
open CategoryTheory Limits AlgebraicGeometry MonoidalCategory
namespace FLT.Mazur.FiniteCoproductTensorRight
set_option backward.isDefEq.respectTransparency false
variable {S : Scheme} {I J : Type} [Finite I] [Finite J]
  (A : I → Over S) (B : J → Over S) (X : Over S)

/-- Descend component maps while retaining the entire second factor. -/
def desc {Y : Over S} (f : ∀ i, A i ⊗ X ⟶ Y) : (∐ A) ⊗ X ⟶ Y :=
  (∐ A) ◁ Sigma.ι (fun _ : Unit ↦ X) () ≫
    (PolygonSplitGroup.productCofanIsColimit A (fun _ : Unit ↦ X)).desc
      (Cofan.mk Y fun p ↦ f p.1)

/-- Restriction to an original component recovers its prescribed map. -/
@[reassoc] theorem component_desc {Y : Over S} (f : ∀ i, A i ⊗ X ⟶ Y) (i : I) :
    Sigma.ι A i ▷ X ≫ desc A X f = f i := by
  rw [desc, ← Category.assoc, ← tensorHom_def]
  exact (PolygonSplitGroup.productCofanIsColimit A (fun _ : Unit ↦ X)).fac _ ⟨i, ()⟩

/-- Component restrictions determine a map from the tensor with the entire second factor. -/
theorem hom_ext {Y : Over S} {f g : (∐ A) ⊗ X ⟶ Y}
    (h : ∀ i, Sigma.ι A i ▷ X ≫ f = Sigma.ι A i ▷ X ≫ g) : f = g := by
  let d : (∐ fun _ : Unit ↦ X) ⟶ X := Sigma.desc fun _ ↦ 𝟙 X
  have he : (∐ A) ◁ d ≫ f = (∐ A) ◁ d ≫ g := by
    apply PolygonSplitGroup.tensor_hom_ext A (fun _ : Unit ↦ X)
    intro i j
    simpa only [tensorHom_comp_whiskerLeft_assoc, d, Sigma.ι_comp_desc,
      tensorHom_id] using h i
  have hd : Sigma.ι (fun _ : Unit ↦ X) () ≫ d = 𝟙 X := Sigma.ι_comp_desc _ _
  have hh := congrArg ((∐ A) ◁ Sigma.ι (fun _ : Unit ↦ X) () ≫ ·) he
  simpa only [← Category.assoc, ← whiskerLeft_comp, hd, whiskerLeft_id,
    Category.id_comp] using hh

/-- Pairs of component restrictions detect maps out of the triple tensor. -/
theorem triple_hom_ext {Y : Over S} {f g : ((∐ A) ⊗ (∐ B)) ⊗ X ⟶ Y}
    (h : ∀ i j, (Sigma.ι A i ⊗ₘ Sigma.ι B j) ▷ X ≫ f =
      (Sigma.ι A i ⊗ₘ Sigma.ι B j) ▷ X ≫ g) : f = g := by
  let d : (∐ fun _ : Unit ↦ X) ⟶ X := Sigma.desc fun _ ↦ 𝟙 X
  have he : ((∐ A) ⊗ (∐ B)) ◁ d ≫ f = ((∐ A) ⊗ (∐ B)) ◁ d ≫ g := by
    apply PolygonSplitGroup.triple_hom_ext A B (fun _ : Unit ↦ X)
    intro i j k
    simpa only [tensorHom_comp_whiskerLeft_assoc, d, Sigma.ι_comp_desc,
      tensorHom_id] using h i j
  have hd : Sigma.ι (fun _ : Unit ↦ X) () ≫ d = 𝟙 X := Sigma.ι_comp_desc _ _
  have hh := congrArg (((∐ A) ⊗ (∐ B)) ◁ Sigma.ι (fun _ : Unit ↦ X) () ≫ ·) he
  simpa only [← Category.assoc, ← whiskerLeft_comp, hd, whiskerLeft_id,
    Category.id_comp] using hh

end FLT.Mazur.FiniteCoproductTensorRight
