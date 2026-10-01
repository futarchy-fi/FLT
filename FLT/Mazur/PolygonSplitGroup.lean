/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.MultiplicativeGroupScheme
public import Mathlib.AlgebraicGeometry.Limits
public import Mathlib.Data.ZMod.Basic

/-!
# The split group with n components

Finite coproducts of the multiplicative group form a smooth commutative group
by multiplying coordinates and adding component indices. This constructs the
candidate group; identification with a polygon's smooth locus is separate.

The group-object API uses chosen monoidal products. `component_mul_prod`
inserts their comparison with ordinary categorical products explicitly.
-/

open CategoryTheory Limits AlgebraicGeometry MonObj MonoidalCategory CartesianMonoidalCategory

@[expose] public noncomputable section

universe u

namespace FLT.Mazur.PolygonSplitGroup

section Comparison

variable {S : Scheme.{u}} {I J : Type} [Finite I] [Finite J]
variable (X : I → Over S) (Y : J → Over S)

/-- Products of component charts cover the product of their coproducts. -/
def productCofan : Cofan (fun p : I × J ↦ X p.1 ⊗ Y p.2) :=
  Cofan.mk ((∐ X) ⊗ (∐ Y)) fun p ↦ (Sigma.ι X p.1 ⊗ₘ Sigma.ι Y p.2)

set_option backward.isDefEq.respectTransparency false in
/-- Finite coproducts distribute over chosen products in schemes over a base. -/
def productCofanIsColimit : IsColimit (productCofan X Y) := by
  apply isColimitOfReflects (Over.forget S)
  let a : Cofan (fun i ↦ (X i).left) :=
    Cofan.mk (∐ X).left fun i ↦ (Sigma.ι X i).left
  let b : Cofan (fun j ↦ (Y j).left) :=
    Cofan.mk (∐ Y).left fun j ↦ (Sigma.ι Y j).left
  have ha : IsColimit a := isColimitOfHasCoproductOfPreservesColimit (Over.forget S) X
  have hb : IsColimit b := isColimitOfHasCoproductOfPreservesColimit (Over.forget S) Y
  refine (isColimitMapCoconeCofanMkEquiv (Over.forget S) _ _).symm ?_
  exact (IsUniversalColimit.nonempty_isColimit_prod_of_isPullback
    (FinitaryPreExtensive.isUniversal_finiteCoproducts ha)
    (FinitaryPreExtensive.isUniversal_finiteCoproducts hb)
    (fun i ↦ (X i).hom) (fun j ↦ (Y j).hom) (∐ X).hom (∐ Y).hom
    (fun i j ↦ Over.isPullback_of_binaryFan_isLimit _ (tensorProductIsBinaryProduct (X i) (Y j)))
    (Over.isPullback_of_binaryFan_isLimit _ (tensorProductIsBinaryProduct (∐ X) (∐ Y)))
    (d := Cofan.mk _ fun p ↦ (Sigma.ι X p.1 ⊗ₘ Sigma.ι Y p.2).left) (Iso.refl _)
    (by intro i; exact (Sigma.ι X i).w)
    (by intro j; exact (Sigma.ι Y j).w)
    (by intro i j; simpa only [Category.id_comp] using!
      (congrArg Over.Hom.left (tensorHom_fst (Sigma.ι X i) (Sigma.ι Y j))))
    (by intro i j; simpa only [Category.id_comp] using!
      (congrArg Over.Hom.left (tensorHom_snd (Sigma.ι X i) (Sigma.ι Y j))))).some

/-- The product/coproduct comparison isomorphism. -/
def productIso : (∐ fun p : I × J ↦ X p.1 ⊗ Y p.2) ≅ ((∐ X) ⊗ (∐ Y)) :=
  (coproductIsCoproduct _).coconePointUniqueUpToIso (productCofanIsColimit X Y)

@[reassoc (attr := simp)]
theorem component_productIso (p : I × J) :
    Sigma.ι _ p ≫ (productIso X Y).hom = Sigma.ι X p.1 ⊗ₘ Sigma.ι Y p.2 :=
  (coproductIsCoproduct _).fac (productCofan X Y) ⟨p⟩

theorem tensor_hom_ext {Z : Over S} {f g : ((∐ X) ⊗ (∐ Y)) ⟶ Z}
    (h : ∀ i j, (Sigma.ι X i ⊗ₘ Sigma.ι Y j) ≫ f =
      (Sigma.ι X i ⊗ₘ Sigma.ι Y j) ≫ g) : f = g := by
  apply (productCofanIsColimit X Y).hom_ext
  rintro ⟨i, j⟩
  exact h i j

theorem triple_hom_ext {K : Type} [Finite K] (Z : K → Over S) {W : Over S}
    {f g : ((∐ X) ⊗ (∐ Y)) ⊗ (∐ Z) ⟶ W}
    (h : ∀ i j k, ((Sigma.ι X i ⊗ₘ Sigma.ι Y j) ⊗ₘ Sigma.ι Z k) ≫ f =
      ((Sigma.ι X i ⊗ₘ Sigma.ι Y j) ⊗ₘ Sigma.ι Z k) ≫ g) : f = g := by
  apply (cancel_epi ((productIso X Y).hom ▷ ∐ Z)).mp
  apply tensor_hom_ext (fun p : I × J ↦ X p.1 ⊗ Y p.2) Z
  intro ⟨i, j⟩ k
  simpa only [tensorHom_comp_whiskerRight_assoc, component_productIso] using h i j k

end Comparison

variable (R : Type u) [CommRing R] (n : ℕ) [NeZero n]

/-- The split candidate for the smooth group of an n-gon. -/
abbrev model : Over (Spec (CommRingCat.of R)) :=
  ∐ fun _ : ZMod n ↦ MultiplicativeGroupScheme.gm R

/-- Inclusion of one multiplicative-group component. -/
abbrev component (i : ZMod n) : MultiplicativeGroupScheme.gm R ⟶ model R n :=
  Sigma.ι (fun _ : ZMod n ↦ MultiplicativeGroupScheme.gm R) i

/-- Multiply within the multiplicative group and add the component indices. -/
def multiplication : model R n ⊗ model R n ⟶ model R n :=
  (productCofanIsColimit (fun _ : ZMod n ↦ MultiplicativeGroupScheme.gm R)
    (fun _ : ZMod n ↦ MultiplicativeGroupScheme.gm R)).desc
      (Cofan.mk _ fun p ↦ μ[MultiplicativeGroupScheme.gm R] ≫ component R n (p.1 + p.2))

@[reassoc (attr := simp)]
theorem component_multiplication (i j : ZMod n) :
    (component R n i ⊗ₘ component R n j) ≫ multiplication R n =
      μ[MultiplicativeGroupScheme.gm R] ≫ component R n (i + j) :=
  (productCofanIsColimit (fun _ : ZMod n ↦ MultiplicativeGroupScheme.gm R)
    (fun _ : ZMod n ↦ MultiplicativeGroupScheme.gm R)).fac _ ⟨i, j⟩

@[reassoc (attr := simp)]
theorem lift_component_multiplication {Z : Over (Spec (CommRingCat.of R))}
    (f g : Z ⟶ MultiplicativeGroupScheme.gm R) (i j : ZMod n) :
    lift (f ≫ component R n i) (g ≫ component R n j) ≫ multiplication R n =
      lift f g ≫ μ[MultiplicativeGroupScheme.gm R] ≫ component R n (i + j) := by
  rw [← lift_map_assoc, component_multiplication]

/-- The identity lies in component zero. -/
def identity : 𝟙_ (Over (Spec (CommRingCat.of R))) ⟶ model R n :=
  η[MultiplicativeGroupScheme.gm R] ≫ component R n 0

/-- Invert in the multiplicative group and negate the component index. -/
def inversion : model R n ⟶ model R n :=
  Sigma.desc fun i ↦ ι[MultiplicativeGroupScheme.gm R] ≫ component R n (-i)

omit [NeZero n] in
@[reassoc (attr := simp)]
theorem component_inversion (i : ZMod n) :
    component R n i ≫ inversion R n =
      ι[MultiplicativeGroupScheme.gm R] ≫ component R n (-i) := by
  simp [component, inversion]

theorem identity_mul : identity R n ▷ model R n ≫ multiplication R n =
    (λ_ (model R n)).hom := by
  apply (cancel_epi (λ_ (model R n)).inv).mp
  apply Sigma.hom_ext
  intro i
  simp only [Iso.inv_hom_id, Category.comp_id]
  rw [leftUnitor_inv_naturality_assoc]
  rw [← tensorHom_def'_assoc, identity, ← whiskerRight_comp_tensorHom_assoc,
    component_multiplication]
  simp only [zero_add, ← Category.assoc, MonObj.one_mul, Iso.inv_hom_id, Category.id_comp]

theorem mul_identity : model R n ◁ identity R n ≫ multiplication R n =
    (ρ_ (model R n)).hom := by
  apply (cancel_epi (ρ_ (model R n)).inv).mp
  apply Sigma.hom_ext
  intro i
  simp only [Iso.inv_hom_id, Category.comp_id]
  rw [rightUnitor_inv_naturality_assoc]
  rw [← tensorHom_def_assoc, identity, ← whiskerLeft_comp_tensorHom_assoc,
    component_multiplication]
  simp only [add_zero, ← Category.assoc, MonObj.mul_one, Iso.inv_hom_id, Category.id_comp]

theorem multiplication_assoc :
    multiplication R n ▷ model R n ≫ multiplication R n =
      (α_ (model R n) (model R n) (model R n)).hom ≫
        model R n ◁ multiplication R n ≫ multiplication R n := by
  apply triple_hom_ext (fun _ : ZMod n ↦ MultiplicativeGroupScheme.gm R)
    (fun _ : ZMod n ↦ MultiplicativeGroupScheme.gm R)
    (fun _ : ZMod n ↦ MultiplicativeGroupScheme.gm R)
  intro i j k
  rw [tensorHom_comp_whiskerRight_assoc, component_multiplication,
    ← whiskerRight_comp_tensorHom_assoc, component_multiplication]
  rw [associator_naturality_assoc, tensorHom_comp_whiskerLeft_assoc,
    component_multiplication, ← whiskerLeft_comp_tensorHom_assoc, component_multiplication]
  simp only [← Category.assoc, MonObj.mul_assoc, add_assoc]

instance monObj : MonObj (model R n) where
  one := identity R n
  mul := multiplication R n
  one_mul := identity_mul R n
  mul_one := mul_identity R n
  mul_assoc := multiplication_assoc R n

instance grpObj : GrpObj (model R n) where
  inv := inversion R n
  left_inv := by
    change lift (inversion R n) (𝟙 _) ≫ multiplication R n = toUnit _ ≫ identity R n
    apply Sigma.hom_ext
    intro i
    change component R n i ≫ _ = component R n i ≫ _
    rw [comp_lift_assoc, component_inversion, Category.comp_id]
    rw [← Category.id_comp (component R n i), lift_component_multiplication]
    simp only [neg_add_cancel, GrpObj.left_inv_assoc, identity, Category.id_comp, comp_toUnit_assoc]
  right_inv := by
    change lift (𝟙 _) (inversion R n) ≫ multiplication R n = toUnit _ ≫ identity R n
    apply Sigma.hom_ext
    intro i
    change component R n i ≫ _ = component R n i ≫ _
    rw [comp_lift_assoc, component_inversion, Category.comp_id]
    rw [← Category.id_comp (component R n i), lift_component_multiplication]
    simp only [add_neg_cancel, GrpObj.right_inv_assoc, identity, Category.id_comp,
      comp_toUnit_assoc]

instance commGrpObj : CommGrpObj (model R n) where
  mul_comm := by
    change (β_ (model R n) (model R n)).hom ≫ multiplication R n = multiplication R n
    apply tensor_hom_ext (fun _ : ZMod n ↦ MultiplicativeGroupScheme.gm R)
      (fun _ : ZMod n ↦ MultiplicativeGroupScheme.gm R)
    intro i j
    rw [BraidedCategory.braiding_naturality_assoc, component_multiplication,
      component_multiplication,
      IsCommMonObj.mul_comm_assoc, add_comm]

set_option backward.isDefEq.respectTransparency false in
set_option backward.defeqAttrib.useBackward true in
instance smooth : Smooth (model R n).hom := by
  let F := Over.forget (Spec (CommRingCat.of R))
  let X := fun _ : ZMod n ↦ MultiplicativeGroupScheme.gm R
  apply (MorphismProperty.cancel_left_of_respectsIso (@Smooth)
    (sigmaComparison F X) (model R n).hom).mp
  have h : sigmaComparison F X ≫ (model R n).hom =
      Sigma.desc (fun _ : ZMod n ↦ (MultiplicativeGroupScheme.gm R).hom) := by
    apply Sigma.hom_ext
    intro i
    rw [ι_comp_sigmaComparison_assoc, Sigma.ι_comp_desc]
    exact (Sigma.ι X i).w
  rw [h]
  exact IsZariskiLocalAtSource.sigmaDesc (P := @Smooth) fun _ ↦ inferInstance

@[reassoc (attr := simp)]
theorem component_mul (i j : ZMod n) :
    (component R n i ⊗ₘ component R n j) ≫ μ[model R n] =
      μ[MultiplicativeGroupScheme.gm R] ≫ component R n (i + j) :=
  component_multiplication R n i j

/-- The comparison from categorical products to the chosen group-object products. -/
def productToTensor {S : Scheme.{u}} (A B : Over S) : A ⨯ B ⟶ A ⊗ B :=
  lift Limits.prod.fst Limits.prod.snd

/-- Component multiplication expressed with ordinary categorical products. -/
theorem component_mul_prod (i j : ZMod n) :
    Limits.prod.map (component R n i) (component R n j) ≫
        productToTensor (model R n) (model R n) ≫ μ[model R n] =
      productToTensor (MultiplicativeGroupScheme.gm R) (MultiplicativeGroupScheme.gm R) ≫
        μ[MultiplicativeGroupScheme.gm R] ≫ component R n (i + j) := by
  have h : Limits.prod.map (component R n i) (component R n j) ≫
      productToTensor (model R n) (model R n) =
      productToTensor (MultiplicativeGroupScheme.gm R) (MultiplicativeGroupScheme.gm R) ≫
        (component R n i ⊗ₘ component R n j) := by
    apply CartesianMonoidalCategory.hom_ext <;> simp [productToTensor]
  rw [← Category.assoc, h, Category.assoc, component_mul]

end FLT.Mazur.PolygonSplitGroup
