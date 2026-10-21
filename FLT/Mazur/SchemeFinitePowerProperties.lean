/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.SchemeOverProductProperties
public import Mathlib.Data.Fintype.Option

/-!
# Geometric properties of finite powers over a scheme

Multiplicative properties stable under base change pass to the actual
categorical finite power. No properness of the factors is required.
-/

@[expose] public noncomputable section
open CategoryTheory Limits AlgebraicGeometry
namespace FLT.Mazur.SchemeFinitePower
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false

variable {S : Scheme} (E : Over S)

/-- Split off the new factor of an option-indexed power. -/
def optionIso (A : Type) [Finite A] :
    (∏ᶜ fun _ : Option A => E) ≅ E ⨯ (∏ᶜ fun _ : A => E) where
  hom := prod.lift (Pi.π _ none) (Pi.lift fun a => Pi.π _ (some a))
  inv := Pi.lift fun a => match a with
    | none => prod.fst
    | some a => prod.snd ≫ Pi.π _ a
  hom_inv_id := by
    apply Pi.hom_ext
    intro a
    cases a <;> simp
  inv_hom_id := by
    apply prod.hom_ext
    · simp
    · apply Pi.hom_ext
      intro a
      simp

/-- The empty power is the original base object. -/
def emptyIso : (∏ᶜ fun _ : PEmpty => E) ≅ Over.mk (𝟙 S) where
  hom := Over.homMk (∏ᶜ fun _ : PEmpty => E).hom (Category.comp_id _)
  inv := Pi.lift PEmpty.elim
  hom_inv_id := by
    apply Pi.hom_ext
    intro a
    exact a.elim
  inv_hom_id := by
    apply Over.OverMorphism.ext
    exact
      (Pi.lift (C := Over S) (f := fun _ : PEmpty => E) PEmpty.elim).w

/-- A base-change stable multiplicative property holds on every finite power. -/
theorem property (P : MorphismProperty Scheme) [P.IsMultiplicative]
    [P.IsStableUnderBaseChange] (hE : P E.hom) (A : Type) [Finite A] :
    P (∏ᶜ fun _ : A => E).hom := by
  let _ := Fintype.ofFinite A
  refine Fintype.induction_empty_option
    (P := fun A [Fintype A] => P (∏ᶜ fun _ : A => E).hom) ?_ ?_ ?_ A
  · intro A B _ e hA
    let _ : Fintype A := Fintype.ofEquiv B e.symm
    let i := Pi.whiskerEquiv (f := fun _ : A => E) (g := fun _ : B => E)
      e (fun _ => Iso.refl E)
    rw [← i.inv.w]
    exact P.comp_mem _ _ (P.of_isIso _) hA
  · rw [← (emptyIso E).hom.w]
    exact P.comp_mem _ _ (P.of_isIso _) (P.id_mem S)
  · intro A _ hA
    rw [← (optionIso E A).hom.w, SchemeOverProduct.structure_eq]
    exact P.comp_mem _ _ (P.of_isIso _) (P.comp_mem _ _ (P.of_isIso _)
      (P.comp_mem _ _ (P.pullback_fst _ _ hA) hE))

end FLT.Mazur.SchemeFinitePower
