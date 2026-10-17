/-
Copyright (c) 2026 krandder. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: krandder
-/
module

public import FLT.Mazur.NilpotentAlgebraErrorCommutation
public import FLT.Mazur.LaurentSquareZeroAutomorphism

/-!
# Conjugation of top-order Laurent errors by an actual reciprocal parameter

A complete parameter congruent to inversion has the same action on the top
coefficient layer as inversion. The parameter itself retains all lower terms.
-/

@[expose] public noncomputable section
open scoped LaurentPolynomial
namespace FLT.Mazur.LaurentReciprocalErrorConjugation
open LaurentPolynomial
variable {R : Type*} [CommRing R] (I : Ideal R)
local notation "L" => R[T;T⁻¹]
local notation "J" => Ideal.map (algebraMap R L) I

/-- Laurent inversion preserves every extended coefficient-ideal power. -/
theorem invert_mem_power (r : ℕ) (z : L) (hz : z ∈ J ^ r) : invert z ∈ J ^ r := by
  have h : J ^ r ≤ Ideal.comap invert.toAlgHom.toRingHom (J ^ r) := by
    rw [← Ideal.map_pow]
    apply Ideal.map_le_iff_le_comap.mpr
    intro x hx
    change invert (algebraMap R L x) ∈ Ideal.map (algebraMap R L) (I ^ r)
    rw [AlgEquiv.commutes]
    exact Ideal.mem_map_of_mem _ hx
  exact h hz

/-- The full conjugacy is detected by the original reciprocal reduction of its parameter. -/
theorem conjugation_eq (r : ℕ) (f : L ≃ₐ[R] L) (g : L →ₐ[R] L)
    (hf : ∀ z, f z - invert z ∈ J) (hg : ∀ z, g z - z ∈ J ^ r)
    (hJ : J ^ (1 + r) = ⊥) :
    f.toAlgHom.comp (g.comp f.symm.toAlgHom) =
      invert.toAlgHom.comp (g.comp invert.toAlgHom) := by
  apply NilpotentAlgebraHigherOrderError.conjugation_eq_of_sub_mem I 1 r
    g f invert ?_ hg hJ
  intro z
  have h := invert_mem_power I 1 (f z - invert z) (by simpa only [pow_one] using hf z)
  change invert (f z) - z ∈ J ^ 1
  simpa only [map_sub, involutive_invert z] using h

/-- A square-zero substitution of weight p^r has full coefficient error of order r. -/
theorem subst_sub_mem (p : R) (r : ℕ) (he : (p ^ r) ^ 2 = 0) (v z : L) :
    LaurentSquareZeroAutomorphism.subst (p ^ r) he v z - z ∈
      ((Ideal.span {p}).map (algebraMap R L)) ^ r := by
  apply LaurentNilpotentReparametrization.hom_sub_mem _
    (LaurentSquareZeroAutomorphism.subst (p ^ r) he v) (AlgHom.id R L) ?_ z
  rw [LaurentSquareZeroAutomorphism.subst_T, AlgHom.id_apply, add_sub_cancel_left]
  rw [Ideal.map_span, Set.image_singleton, Ideal.span_singleton_pow,
    Ideal.mem_span_singleton, ← map_pow]
  exact ⟨v, rfl⟩

end FLT.Mazur.LaurentReciprocalErrorConjugation
