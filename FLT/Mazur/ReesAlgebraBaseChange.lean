/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.ReesAlgebraMap
public import Mathlib.RingTheory.TensorProduct.Basic

/-!
# The relative Rees algebra surjects onto the extended-ideal Rees algebra

After arbitrary scalar extension, the actual Rees algebra of the extended
ideal is a quotient of the base-changed Rees algebra. No flatness is needed.
This is the affine closed-immersion comparison for the geometric Rees space.
-/

@[expose] public noncomputable section

open Polynomial
open scoped TensorProduct

namespace FLT.Mazur.Rees

variable {R S : Type*} [CommRing R] [CommRing S] [Algebra R S] (I : Ideal R)

/-- Scalar extension on Rees algebras is linear over the original base. -/
def baseChangeMap :
    reesAlgebra I →ₐ[R] reesAlgebra (I.map (Algebra.algebraMap R S)) where
  toRingHom := algebraMap I _ (Algebra.algebraMap R S) le_rfl
  commutes' r := by
    apply Subtype.ext
    exact Polynomial.map_C _

/-- The relative algebra maps to the actual extended-ideal Rees algebra. -/
def relativeMap :
    S ⊗[R] reesAlgebra I →ₐ[S] reesAlgebra (I.map (Algebra.algebraMap R S)) :=
  AlgHom.liftEquiv R S _ _ (baseChangeMap (S := S) I)

/-- Pure tensors retain the original scalar and coefficient maps. -/
lemma relativeMap_tmul (s : S) (p : reesAlgebra I) :
    relativeMap I (s ⊗ₜ[R] p) = s • baseChangeMap I p := rfl

/-- The relative comparison followed by the inclusion into ordinary polynomials. -/
def relativePolynomialMap : S ⊗[R] reesAlgebra I →ₐ[S] S[X] :=
  (reesAlgebra (I.map (Algebra.algebraMap R S))).val.comp (relativeMap I)

/-- Monomials of extended ideal powers lift through the relative algebra. -/
lemma monomial_mem_relative_range (n : ℕ) (s : S)
    (hs : s ∈ (I.map (Algebra.algebraMap R S)) ^ n) :
    Polynomial.monomial n s ∈ (relativePolynomialMap (S := S) I).range := by
  let P : Ideal S := (relativePolynomialMap (S := S) I).range.toSubmodule.comap
    (Polynomial.monomial n)
  have hle : (I ^ n).map (Algebra.algebraMap R S) ≤ P := by
    apply Ideal.map_le_iff_le_comap.mpr
    intro r hr
    refine ⟨1 ⊗ₜ[R] ⟨Polynomial.monomial n r, reesAlgebra.monomial_mem.mpr hr⟩, ?_⟩
    change (relativeMap I
      (1 ⊗ₜ[R] ⟨Polynomial.monomial n r, reesAlgebra.monomial_mem.mpr hr⟩)).val = _
    rw [relativeMap_tmul, one_smul]
    exact Polynomial.map_monomial (Algebra.algebraMap R S)
  apply hle
  rwa [Ideal.map_pow]

/-- Every polynomial with coefficients in the extended powers comes from the relative algebra. -/
theorem relativeMap_surjective : Function.Surjective (relativeMap (S := S) I) := by
  classical
  intro p
  have hp : p.val ∈ (relativePolynomialMap (S := S) I).range := by
    rw [p.val.as_sum_support]
    exact Subalgebra.sum_mem _ (fun n _ ↦ monomial_mem_relative_range I n _ (p.property n))
  obtain ⟨x, hx⟩ := hp
  exact ⟨x, Subtype.ext hx⟩

/-- The actual extended Rees algebra is finite over the relative algebra. -/
theorem relativeMap_finite : (relativeMap (S := S) I).Finite :=
  AlgHom.Finite.of_surjective _ (relativeMap_surjective I)

end FLT.Mazur.Rees
