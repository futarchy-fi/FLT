/-
Copyright (c) 2026 krandder. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: krandder
-/
module

public import FLT.Mazur.PolygonArithmeticLaurentSystemRestriction
public import FLT.Mazur.LaurentNilpotentReparametrization

/-!
# Restrict a complete Laurent identity to every earlier arithmetic layer

Naturality on the positive generator suffices because Laurent algebra maps are
determined by that generator. No coefficient-surjectivity choice is needed.
-/

@[expose] public noncomputable section
open scoped LaurentPolynomial
namespace FLT.Mazur.PolygonArithmeticStages
open LaurentPolynomial PolygonScalingNaturality
variable {R : Type*} [CommRing R] {π : R}
variable (a : (m : ℕ) → (Quotient R π m)[T;T⁻¹] →ₐ[Quotient R π m] (Quotient R π m)[T;T⁻¹])
  (ha : ∀ m, (coeffMap (restriction R π m).toRingHom).comp (a (m + 1)).toRingHom =
    (a m).toRingHom.comp (coeffMap (restriction R π m).toRingHom))

include ha

/-- A full identity at any arithmetic order remains identity at every earlier order. -/
theorem laurentSystem_identity_restriction {k m : ℕ} (h : k ≤ m)
    (hm : a m = AlgHom.id (Quotient R π m) _) :
    a k = AlgHom.id (Quotient R π k) _ := by
  apply LaurentNilpotentReparametrization.hom_ext_positive
  have he := DFunLike.congr_fun (laurentSystem_restrictionLE a ha h) (T 1)
  simpa only [hm, RingHom.comp_apply, AlgHom.toRingHom_eq_coe,
    RingHom.coe_coe, AlgHom.id_apply, coeffMap_T_one] using he.symm

end FLT.Mazur.PolygonArithmeticStages
