/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import Mathlib.RingTheory.ReesAlgebra
public import Mathlib.Algebra.DirectSum.Internal

/-!
# Homogeneous coordinates on the Rees algebra

The direct sum of the actual ideal powers is the polynomial Rees algebra
as a ring. This equivalence lets homogeneous actions assemble without
choosing preimages of cohomology image classes.
-/

@[expose] public noncomputable section

open scoped DirectSum

namespace FLT.Mazur.Rees

variable {R : Type*} [CommRing R] (J : Ideal R)

/-- A homogeneous ideal element as a Rees monomial. -/
def monomial (n : ℕ) : ↥(J ^ n) →+ reesAlgebra J where
  toFun r := ⟨Polynomial.monomial n r, reesAlgebra.monomial_mem.mpr r.property⟩
  map_zero' := Subtype.ext (map_zero _)
  map_add' _ _ := Subtype.ext (map_add _ _ _)

/-- Assemble homogeneous ideal elements in the polynomial Rees ring. -/
def sumRingHom : (⨁ n : ℕ, ↥(J ^ n)) →+* reesAlgebra J :=
  DirectSum.toSemiring (monomial J)
    (Subtype.ext (Polynomial.monomial_zero_one))
    (fun _ _ ↦ Subtype.ext (Polynomial.monomial_mul_monomial _ _ _ _).symm)

/-- Assembly sends a homogeneous element to its original monomial. -/
lemma sumRingHom_of (n : ℕ) (r : ↥(J ^ n)) :
    sumRingHom J (DirectSum.of (fun n ↦ ↥(J ^ n)) n r) = monomial J n r :=
  DirectSum.toSemiring_of _ _ _ _ _

/-- The n-th coefficient is exactly the original n-th summand. -/
lemma sumRingHom_coeff (x : ⨁ n : ℕ, ↥(J ^ n)) (n : ℕ) :
    ((sumRingHom J x).val).coeff n = (x n).val := by
  classical
  induction x using DirectSum.induction_on with
  | zero => rfl
  | add x y hx hy =>
    change ((sumRingHom J (x + y)).val).coeff n = _
    rw [map_add]
    change ((sumRingHom J x).val + (sumRingHom J y).val).coeff n = _
    rw [Polynomial.coeff_add, hx, hy]
    rfl
  | of k r =>
    rw [sumRingHom_of]
    change (Polynomial.monomial k r.val).coeff n = _
    by_cases h : k = n
    · subst n
      simp only [Polynomial.coeff_monomial, ite_true, DirectSum.of_eq_same]
    · simp only [Polynomial.coeff_monomial, ite_eq_right h,
        DirectSum.of_eq_of_ne _ _ _ (Ne.symm h)]
      rfl

/-- Homogeneous coordinates distinguish Rees elements. -/
lemma sumRingHom_injective : Function.Injective (sumRingHom J) := by
  intro x y h
  ext n
  simpa only [sumRingHom_coeff] using
    congrArg (fun p : reesAlgebra J ↦ p.val.coeff n) h

/-- Every Rees polynomial assembles from its actual ideal-power coefficients. -/
lemma sumRingHom_surjective : Function.Surjective (sumRingHom J) := by
  classical
  intro p
  refine ⟨∑ n ∈ p.val.support,
    DirectSum.of (fun n ↦ ↥(J ^ n)) n ⟨p.val.coeff n, p.property n⟩, ?_⟩
  apply Subtype.ext
  simp only [map_sum, sumRingHom_of, AddSubmonoidClass.coe_finsetSum, monomial]
  exact Polynomial.sum_monomial_eq p.val

/-- Ring coordinates for the original polynomial Rees algebra. -/
def sumRingEquiv : (⨁ n : ℕ, ↥(J ^ n)) ≃+* reesAlgebra J :=
  RingEquiv.ofBijective (sumRingHom J)
    ⟨sumRingHom_injective J, sumRingHom_surjective J⟩

end FLT.Mazur.Rees
