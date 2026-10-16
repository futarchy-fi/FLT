/-
Copyright (c) 2026 krandder. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: krandder
-/
module

public import FLT.Mazur.LaurentNilpotentReparametrization
public import FLT.Mazur.LaurentScaledCoordinateIsomorphisms

/-!
# Full Laurent automorphisms with a scaled reciprocal reduction

Every unit congruent to a/T, for an original coefficient unit a, gives an
actual automorphism. The inverse is constructed at every nilpotent order.
-/

@[expose] public noncomputable section
open scoped LaurentPolynomial
namespace FLT.Mazur.LaurentScaledNilpotentReparametrization
variable {R : Type*} [CommRing R] (I : Ideal R) (hI : IsNilpotent I)
  (a : Rˣ) (u : R[T;T⁻¹]ˣ)
  (hu : (u : R[T;T⁻¹]) - algebraMap R R[T;T⁻¹] (a : R) * LaurentPolynomial.T (-1) ∈
    I.map (algebraMap R R[T;T⁻¹]))
local notation "L" => R[T;T⁻¹]
include hu hI

/-- The full scaled reciprocal substitution is bijective, retaining all nilpotent terms. -/
theorem evalUnit_bijective : Function.Bijective (LaurentUnitPoints.evalUnit (R := R) u) := by
  let f := LaurentUnitPoints.evalUnit (R := R) u
  let g := PolygonScaledReciprocal.reciprocal a
  have hg : Function.Involutive g := PolygonScaledReciprocal.reciprocal_involutive a
  have h : ∀ x : L, f x - g x ∈ I.map (algebraMap R L) := by
    refine LaurentNilpotentReparametrization.hom_sub_mem _ f g ?_
    simpa only [f, g, LaurentUnitPoints.evalUnit_T, zpow_one,
      PolygonScaledReciprocal.reciprocal_T, LaurentPolynomial.C_eq_algebraMap] using hu
  have hi : ∀ x : L, (f.comp g) x - x ∈ I.map (algebraMap R L) := by
    intro x
    simpa only [AlgHom.comp_apply, hg x] using h (g x)
  have hb := NilpotentAlgebraAutomorphism.bijective I (f.comp g) hi hI
  exact ⟨fun x y hxy ↦ by
      apply hg.injective
      apply hb.1
      simpa only [AlgHom.comp_apply, hg x, hg y] using hxy,
    fun y ↦ by
      obtain ⟨x, hx⟩ := hb.2 y
      exact ⟨g x, hx⟩⟩

/-- The actual Laurent algebra isomorphism for the full, independently given unit. -/
def equiv : L ≃ₐ[R] L :=
  AlgEquiv.ofBijective (LaurentUnitPoints.evalUnit u) (evalUnit_bijective I hI a u hu)

/-- The isomorphism evaluates at the entire original parameter, without truncation. -/
theorem equiv_toAlgHom : (equiv I hI a u hu).toAlgHom = LaurentUnitPoints.evalUnit u := rfl

/-- The positive coordinate is the full original unit. -/
theorem equiv_T : equiv I hI a u hu (LaurentPolynomial.T 1) = (u : L) := by
  change LaurentUnitPoints.evalUnit u (LaurentPolynomial.T 1) = _
  rw [LaurentUnitPoints.evalUnit_T, zpow_one]

end FLT.Mazur.LaurentScaledNilpotentReparametrization
