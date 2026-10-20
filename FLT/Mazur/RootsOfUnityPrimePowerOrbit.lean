/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.RootsOfUnityLaurentKernel
public import FLT.Mazur.LaurentIdentityIdeal
public import Mathlib.Algebra.CharP.Lemmas
public import Mathlib.Algebra.CharP.Algebra

/-!
# The full prime-power orbit equation in characteristic p

The roots-of-unity ideal is the power of the identity ideal, including over
nonreduced coefficient rings. This retains the multiplicity of the coincident
identity sections instead of replacing the subgroup by its reduced support.
-/

@[expose] public noncomputable section

open LaurentPolynomial
open scoped LaurentPolynomial

namespace FLT.Mazur.RootsOfUnityPrimePowerOrbit

variable (R : Type*) [CommRing R] (p : ℕ) [Fact p.Prime] [CharP R p]

/-- In characteristic p the prime-power equation is the repeated identity equation. -/
theorem equation (r : ℕ) :
    T ((p ^ r : ℕ) : ℤ) - (1 : R[T;T⁻¹]) = (T 1 - 1) ^ p ^ r := by
  let _ : CharP R[T;T⁻¹] p := charP_of_injective_algebraMap' R p
  rw [sub_pow_char_pow, one_pow, T_pow]
  simp

/-- The actual Laurent evaluation at the identity has its expected full kernel. -/
theorem identity_kernel :
    RingHom.ker (LaurentUnitPoints.evalUnit (R := R) (1 : Rˣ)).toRingHom =
      Ideal.span {T 1 - (1 : R[T;T⁻¹])} := by
  ext f
  exact (LaurentIdentityIdeal.evalOne_eq_zero_iff f).trans Ideal.mem_span_singleton.symm

/-- The full subgroup kernel is the prime-power power of the identity kernel. -/
theorem kernel (r : ℕ) :
    RingHom.ker (RootsOfUnityAlgebra.restriction R (p ^ r)).toAlgHom.toRingHom =
      (RingHom.ker (LaurentUnitPoints.evalUnit (R := R) (1 : Rˣ)).toRingHom) ^ p ^ r := by
  rw [RootsOfUnityLaurentKernel.kernel, identity_kernel, Ideal.span_singleton_pow, equation]

/-- Equivalently, the subgroup ideal is the product of all coincident identity ideals. -/
theorem kernel_product (r : ℕ) :
    RingHom.ker (RootsOfUnityAlgebra.restriction R (p ^ r)).toAlgHom.toRingHom =
      ∏ _ : Fin (p ^ r),
        RingHom.ker (LaurentUnitPoints.evalUnit (R := R) (1 : Rˣ)).toRingHom := by
  rw [kernel]
  simp

end FLT.Mazur.RootsOfUnityPrimePowerOrbit
