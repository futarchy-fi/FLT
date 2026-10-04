/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.AffineIntegerModel
public import Mathlib.RingTheory.Localization.BaseChange

/-!
# Principal open charts of integer models

A principal open chart of an affine model is an open immersion already at
the finite stage. Its base change is the corresponding principal open of
the original algebra. This constructs principal charts; it does not assert
that an arbitrary descended overlap map is an open immersion.
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
open scoped TensorProduct

namespace FLT.Mazur.Approximation

universe u

variable {A₀ A B₀ B : Type u}
  [CommRing A₀] [CommRing A] [CommRing B₀] [CommRing B]
  [Algebra A₀ A] [Algebra A₀ B₀] [Algebra A B]

/-- Localization of an integer model recovers the corresponding principal
localization after scalar extension. -/
def principalIntegerModelEquiv (e : A ⊗[A₀] B₀ ≃ₐ[A] B) (x : B₀) :
    A ⊗[A₀] Localization.Away x ≃ₐ[A] Localization.Away (e (1 ⊗ₜ x)) :=
  (IsLocalization.Away.tensorProductEquivTMulRight A₀ A x (Localization.Away x)).trans
    (IsLocalization.algEquivOfAlgEquiv
      (M := Submonoid.powers ((1 : A) ⊗ₜ[A₀] x))
      (T := Submonoid.powers (e (1 ⊗ₜ x)))
      (Localization.Away ((1 : A) ⊗ₜ[A₀] x)) (Localization.Away (e (1 ⊗ₜ x)))
      e (by simp [Submonoid.map_powers]))

/-- The localization comparison commutes with the original chart maps. -/
@[simp]
theorem principalIntegerModelEquiv_tmul (e : A ⊗[A₀] B₀ ≃ₐ[A] B) (x b : B₀) (a : A) :
    principalIntegerModelEquiv e x (a ⊗ₜ algebraMap B₀ (Localization.Away x) b) =
      algebraMap B (Localization.Away (e (1 ⊗ₜ x))) (e (a ⊗ₜ b)) := by
  simp only [principalIntegerModelEquiv, AlgEquiv.trans_apply,
    IsLocalization.Away.tensorProductEquivTMulRight_tmul,
    IsLocalization.algEquivOfAlgEquiv_eq]

/-- Each principal chart of the model is an open immersion before base change. -/
theorem principalIntegerModel_isOpenImmersion (x : B₀) :
    IsOpenImmersion (Spec.map (CommRingCat.ofHom
      (algebraMap B₀ (Localization.Away x)))) :=
  IsOpenImmersion.of_isLocalization x

/-- The principal chart model has a cartesian square over the coefficient base. -/
theorem principalIntegerModel_isPullback (e : A ⊗[A₀] B₀ ≃ₐ[A] B) (x : B₀) :
    IsPullback
      (Spec.map (CommRingCat.ofHom ((principalIntegerModelEquiv e x).toRingHom.comp
        Algebra.TensorProduct.includeRight.toRingHom)))
      (Spec.map (CommRingCat.ofHom (algebraMap A (Localization.Away (e (1 ⊗ₜ x))))))
      (Spec.map (CommRingCat.ofHom (algebraMap A₀ (Localization.Away x))))
      (Spec.map (CommRingCat.ofHom (algebraMap A₀ A))) :=
  integerModel_isPullback (principalIntegerModelEquiv e x)

end FLT.Mazur.Approximation
