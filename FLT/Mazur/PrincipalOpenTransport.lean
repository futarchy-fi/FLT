/-
Copyright (c) 2026 krandder. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: krandder
-/
module

public import Mathlib.RingTheory.Localization.Away.Basic

/-!
# Transport of actual principal opens

An algebra equivalence preserving a specified function identifies its actual
principal localizations, with the restriction square on all original functions.
-/

@[expose] public noncomputable section
namespace FLT.Mazur.PrincipalOpenTransport
variable {R A B : Type*} [CommRing R] [CommRing A] [CommRing B]
  [Algebra R A] [Algebra R B] (e : A ≃ₐ[R] B) (x : A) (y : B) (h : e x = y)

/-- Transport the actual principal localization along its coordinate equivalence. -/
def equiv : Localization.Away x ≃ₐ[R] Localization.Away y :=
  IsLocalization.algEquivOfAlgEquiv (M := Submonoid.powers x)
    (T := Submonoid.powers y) _ _ e (by rw [Submonoid.map_powers, h])

/-- The localization equivalence commutes with restriction of every function. -/
@[simp] theorem equiv_base (z : A) :
    equiv e x y h (algebraMap A (Localization.Away x) z) =
      algebraMap B (Localization.Away y) (e z) :=
  IsLocalization.algEquivOfAlgEquiv_eq _ _

/-- Its inverse retains the reverse restriction square. -/
@[simp] theorem equiv_symm_base (z : B) :
    (equiv e x y h).symm (algebraMap B (Localization.Away y) z) =
      algebraMap A (Localization.Away x) (e.symm z) := by
  apply (equiv e x y h).injective
  rw [AlgEquiv.apply_symm_apply, equiv_base, AlgEquiv.apply_symm_apply]

end FLT.Mazur.PrincipalOpenTransport
