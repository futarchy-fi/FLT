/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.AuxiliaryLevelHomScheme
public import FLT.Mazur.ChowProjectiveProduct

/-!
# Properness of the actual finite marking power

Identify the categorical power used by the marking equations with the
constructed iterated proper relative product. This proves properness for the
original power, without replacing its projections or parameter scheme.
-/

@[expose] public noncomputable section
open CategoryTheory Limits AlgebraicGeometry
namespace FLT.Mazur.AuxiliaryLevel
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false

variable {S : Scheme} (E : Over S) [IsProper E.hom] (A : Type) [Fintype A]

/-- The explicit iterated proper product with one factor for each label. -/
def properPowerData :=
  Chow.finProperProduct S (Fintype.card A) (fun _ => E.left)
    (fun _ => E.hom) (fun _ => inferInstance)

/-- The iterated product, regarded over the original base. -/
def properPower : Over S := Over.mk (properPowerData E A).base

/-- The actual categorical marking power is the iterated proper product. -/
def markingPowerProperIso : (∏ᶜ fun _ : A => E) ≅ properPower E A where
  hom := Over.homMk ((properPowerData E A).lift (∏ᶜ fun _ : A => E).hom
    (fun i => (Pi.π (fun _ : A => E) ((Fintype.equivFin A).symm i)).left)
    (fun _ => Over.w _)) ((properPowerData E A).lift_base _ _ _)
  inv := Pi.lift fun a => Over.homMk
    ((properPowerData E A).π (Fintype.equivFin A a))
    ((properPowerData E A).π_base _)
  hom_inv_id := by
    apply Pi.hom_ext
    intro a
    apply Over.OverMorphism.ext
    simp only [Category.assoc, Pi.lift_comp_π, Over.comp_left,
      Over.homMk_left, properPowerData, Chow.ProperRelativeProduct.lift_π,
      Equiv.symm_apply_apply, Category.id_comp]
  inv_hom_id := by
    apply Over.OverMorphism.ext
    apply (properPowerData E A).hom_ext
    · change _ ≫ (properPower E A).hom = _
      rw [Over.w]
      rfl
    · intro i
      simp only [Over.comp_left, Over.homMk_left, Category.assoc,
        Chow.ProperRelativeProduct.lift_π, Over.id_left, Category.id_comp]
      have h := congrArg (fun f => f.left)
        (Pi.lift_comp_π (fun a => (Over.homMk
          ((properPowerData E A).π (Fintype.equivFin A a))
          ((properPowerData E A).π_base _) : properPower E A ⟶ E))
          ((Fintype.equivFin A).symm i))
      simpa only [Over.comp_left, Over.homMk_left, Equiv.apply_symm_apply] using h

omit [Fintype A] in
/-- Properness of the categorical power follows from the explicit comparison. -/
instance markingPower_isProper [Finite A] : IsProper (∏ᶜ fun _ : A => E).hom := by
  let _ := Fintype.ofFinite A
  let _ : IsProper (properPower E A).hom := (properPowerData E A).proper
  rw [← (markingPowerProperIso E A).hom.w]
  infer_instance

end FLT.Mazur.AuxiliaryLevel
