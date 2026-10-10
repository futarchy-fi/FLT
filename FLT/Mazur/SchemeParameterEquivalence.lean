/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import Mathlib.AlgebraicGeometry.Scheme

/-!
# Recovering actual scheme isomorphisms from natural parameter equivalences

Evaluate a natural equivalence of all parameters over a base at the identity
parameter. The resulting actual scheme morphism induces every component of
the equivalence. Its inverse and composition laws follow by parameter
injectivity. This is the explicit relative Yoneda argument used for overlaps.
-/

@[expose] public noncomputable section

open CategoryTheory AlgebraicGeometry

universe u

namespace FLT.Mazur.OpenIdealCover

variable {H K S : Scheme.{u}} (p : H ⟶ S) (q : K ⟶ S)
variable (E : ∀ {X : Scheme.{u}} (s : X ⟶ S),
  { f : X ⟶ H // f ≫ p = s } ≃ { f : X ⟶ K // f ≫ q = s })
variable (hE : ∀ {X Y : Scheme.{u}} (s : X ⟶ S) (t : Y ⟶ S)
  (g : Y ⟶ X) (hg : g ≫ s = t) (f : { f : X ⟶ H // f ≫ p = s }),
  (E t ⟨g ≫ f.val, (Category.assoc _ _ _).trans
    ((congrArg (g ≫ ·) f.property).trans hg)⟩).val = g ≫ (E s f).val)

/-- Evaluate the natural parameter equivalence on the identity of its source representative. -/
def schemeParameterEquivMap : H ⟶ K := (E p ⟨𝟙 _, Category.id_comp _⟩).val

/-- The resulting actual scheme morphism lies over the original coefficient base. -/
theorem schemeParameterEquivMap_over : schemeParameterEquivMap p q E ≫ q = p :=
  (E p ⟨𝟙 _, Category.id_comp _⟩).property

include hE in
/-- Every component of the natural equivalence is composition with the constructed scheme map. -/
theorem schemeParameterEquiv_apply {X : Scheme.{u}} (s : X ⟶ S)
    (f : { f : X ⟶ H // f ≫ p = s }) :
    (E s f).val = f.val ≫ schemeParameterEquivMap p q E := by
  have h := hE p s f.val f.property ⟨𝟙 _, Category.id_comp _⟩
  simpa only [Category.comp_id, schemeParameterEquivMap] using h

/-- A natural equivalence of all relative scheme parameters gives an actual scheme isomorphism. -/
def schemeParameterEquivIso : H ≅ K where
  hom := schemeParameterEquivMap p q E
  inv := ((E q).symm ⟨𝟙 _, Category.id_comp _⟩).val
  hom_inv_id := by
    let k := (E q).symm ⟨𝟙 _, Category.id_comp _⟩
    have hk : (E q k).val = 𝟙 K := congrArg Subtype.val (Equiv.apply_symm_apply _ _)
    let f : { f : H ⟶ H // f ≫ p = p } :=
      ⟨schemeParameterEquivMap p q E ≫ k.val, by
        rw [Category.assoc, k.property, schemeParameterEquivMap_over]⟩
    have hf : E p f = E p ⟨𝟙 _, Category.id_comp _⟩ := by
      apply Subtype.ext
      have hh := hE q p (schemeParameterEquivMap p q E)
        (schemeParameterEquivMap_over p q E) k
      rw [hk, Category.comp_id] at hh
      exact hh
    exact congrArg Subtype.val ((E p).injective hf)
  inv_hom_id := by
    have h := schemeParameterEquiv_apply p q E hE q
      ((E q).symm ⟨𝟙 _, Category.id_comp _⟩)
    rw [Equiv.apply_symm_apply] at h
    exact h.symm

/-- The isomorphism constructed from relative parameters retains the structure map. -/
theorem schemeParameterEquivIso_over : (schemeParameterEquivIso p q E hE).hom ≫ q = p :=
  schemeParameterEquivMap_over p q E

end FLT.Mazur.OpenIdealCover
