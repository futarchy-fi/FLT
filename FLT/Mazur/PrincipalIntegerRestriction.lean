/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.PrincipalOpenIntegerModel
public import FLT.Mazur.LocalizationJointRestriction

/-!
# Canonical restrictions and recovery of principal integer models

The localized map is constructed from the original algebra map. Agreement on
unlocalized elements determines its recovery on every localized element.
-/

@[expose] public noncomputable section

set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

open scoped TensorProduct

namespace FLT.Mazur.Approximation

universe u

/-- The canonical localized algebra map, allowing an explicitly identified denominator. -/
def principalRestrictionAlgHom {R B C : Type u} [CommRing R] [CommRing B] [CommRing C]
    [Algebra R B] [Algebra R C] (f : B →ₐ[R] C) (x : B) (y : C) (h : f x = y) :
    Localization.Away x →ₐ[R] Localization.Away y :=
  IsLocalization.Away.liftAlgHom x
    (f := (IsScalarTower.toAlgHom R C (Localization.Away y)).comp f)
    (by
      change IsUnit (algebraMap C (Localization.Away y) (f x))
      rw [h]
      exact IsLocalization.Away.algebraMap_isUnit y)

/-- Canonical restriction retains the unlocalized chart map. -/
@[simp]
theorem principalRestrictionAlgHom_algebraMap {R B C : Type u}
    [CommRing R] [CommRing B] [CommRing C] [Algebra R B] [Algebra R C]
    (f : B →ₐ[R] C) (x : B) (y : C) (h : f x = y) (b : B) :
    principalRestrictionAlgHom f x y h (algebraMap B (Localization.Away x) b) =
      algebraMap C (Localization.Away y) (f b) := by
  simp [principalRestrictionAlgHom]

/-- With its natural denominator the algebra map is the usual ring restriction. -/
theorem principalRestrictionAlgHom_toRingHom {R B C : Type u}
    [CommRing R] [CommRing B] [CommRing C] [Algebra R B] [Algebra R C]
    (f : B →ₐ[R] C) (x : B) :
    (principalRestrictionAlgHom f x (f x) rfl).toRingHom =
      LocalizationJointRestriction.restriction f.toRingHom x := by
  apply IsLocalization.ringHom_ext (Submonoid.powers x)
  ext b
  exact principalRestrictionAlgHom_algebraMap f x (f x) rfl b |>.trans
    (LocalizationJointRestriction.restriction_algebraMap f.toRingHom x b).symm

/-- Recovery of a localized map follows from its values on chart elements. -/
theorem principalIntegerModel_restriction_recovery
    {R A B₀ C₀ B C : Type u} [CommRing R] [CommRing A]
    [CommRing B₀] [CommRing C₀] [CommRing B] [CommRing C]
    [Algebra R A] [Algebra R B₀] [Algebra R C₀] [Algebra A B] [Algebra A C]
    (eB : A ⊗[R] B₀ ≃ₐ[A] B) (eC : A ⊗[R] C₀ ≃ₐ[A] C)
    (f : B₀ →ₐ[R] C₀) (x : B₀) (y : C₀) (h : f x = y)
    (g : Localization.Away (eB (1 ⊗ₜ x)) →ₐ[A]
      Localization.Away (eC (1 ⊗ₜ y)))
    (hg : ∀ b, g (algebraMap B _ (eB (1 ⊗ₜ b))) =
      algebraMap C _ (eC (1 ⊗ₜ f b))) (c : Localization.Away x) :
    principalIntegerModelEquiv eC y (1 ⊗ₜ principalRestrictionAlgHom f x y h c) =
      g (principalIntegerModelEquiv eB x (1 ⊗ₜ c)) := by
  let l := ((principalIntegerModelEquiv eC y).toRingHom.comp
    Algebra.TensorProduct.includeRight.toRingHom).comp
      (principalRestrictionAlgHom f x y h).toRingHom
  let r := g.toRingHom.comp ((principalIntegerModelEquiv eB x).toRingHom.comp
    Algebra.TensorProduct.includeRight.toRingHom)
  have heq : l = r := by
    apply IsLocalization.ringHom_ext (Submonoid.powers x)
    ext b
    change principalIntegerModelEquiv eC y
      (1 ⊗ₜ principalRestrictionAlgHom f x y h (algebraMap _ _ b)) =
        g (principalIntegerModelEquiv eB x (1 ⊗ₜ algebraMap _ _ b))
    rw [principalRestrictionAlgHom_algebraMap, principalIntegerModelEquiv_tmul,
      principalIntegerModelEquiv_tmul, hg]
  exact RingHom.congr_fun heq c

end FLT.Mazur.Approximation
