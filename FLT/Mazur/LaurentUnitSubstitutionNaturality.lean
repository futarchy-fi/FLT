/-
Copyright (c) 2026 krandder. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: krandder
-/
module

public import FLT.Mazur.LaurentNearIdentityAutomorphism
public import FLT.Mazur.PolygonScalingNaturality

/-!
# Coefficient squares for full Laurent substitutions and their inverses

The forward square follows from the actual coordinate unit. Injectivity then
forces the inverse square, independently of how the inverse was constructed.
-/

@[expose] public noncomputable section
open scoped LaurentPolynomial
namespace FLT.Mazur.LaurentUnitSubstitutionNaturality
open LaurentPolynomial LaurentUnitPoints PolygonScalingNaturality
set_option backward.isDefEq.respectTransparency false
variable {R S : Type*} [CommRing R] [CommRing S] (f : R →+* S)

/-- Coefficient change commutes with substitution at the full mapped Laurent unit. -/
theorem evalUnit_coeffMap (u : R[T;T⁻¹]ˣ) :
    (coeffMap f).comp (evalUnit (R := R) u).toRingHom =
      (evalUnit (R := S) (Units.map (coeffMap f) u)).toRingHom.comp (coeffMap f) := by
  apply ringHom_ext <;> simp [← map_inv]

/-- An equality of full coordinate units supplies the entire forward coefficient square. -/
theorem equiv_naturality (a : R[T;T⁻¹] ≃ₐ[R] R[T;T⁻¹])
    (b : S[T;T⁻¹] ≃ₐ[S] S[T;T⁻¹])
    (h : Units.map (coeffMap f) (pointUnit a.toAlgHom) = pointUnit b.toAlgHom) :
    (coeffMap f).comp a.toAlgHom.toRingHom =
      b.toAlgHom.toRingHom.comp (coeffMap f) := by
  have he := evalUnit_coeffMap f (pointUnit a.toAlgHom)
  rwa [evalUnit_pointUnit, h, evalUnit_pointUnit] at he

/-- The full inverse square follows from the forward one without inverse choices. -/
theorem symm_naturality (a : R[T;T⁻¹] ≃ₐ[R] R[T;T⁻¹])
    (b : S[T;T⁻¹] ≃ₐ[S] S[T;T⁻¹])
    (h : (coeffMap f).comp a.toAlgHom.toRingHom =
      b.toAlgHom.toRingHom.comp (coeffMap f)) :
    (coeffMap f).comp a.symm.toAlgHom.toRingHom =
      b.symm.toAlgHom.toRingHom.comp (coeffMap f) := by
  apply RingHom.ext
  intro x
  apply b.injective
  have hx := DFunLike.congr_fun h (a.symm x)
  simpa only [RingHom.comp_apply, AlgHom.toRingHom_eq_coe, AlgHom.coe_toRingHom,
    AlgEquiv.coe_toAlgHom, AlgEquiv.apply_symm_apply] using hx.symm

end FLT.Mazur.LaurentUnitSubstitutionNaturality
