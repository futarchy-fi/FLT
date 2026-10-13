/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import Mathlib.RingTheory.Norm.Basic
public import Mathlib.RingTheory.TensorProduct.Basic
public import Mathlib.LinearAlgebra.TensorProduct.Basis

/-!
# Genuine finite-free norms for translation coefficients

The explicit finite basis prevents the fallback value of `Algebra.norm` from
being used outside the finite-free locus. Norms commute with arbitrary scalar
extension, including residue fields and noninjective coefficient maps. This
is the algebraic input for norms on local finite translation charts; it does
not extend a coaction from an open subscheme to its affine envelope.
-/

@[expose] public noncomputable section
open Module TensorProduct
namespace FLT.Mazur.FiniteFreeTranslationNorm
universe u v w
variable {R : Type u} {S : Type v} [CommRing R] [CommRing S] [Algebra R S]
  {ι : Type w} [Finite ι] (b : Basis ι R S)
include b

/-- With an actual finite basis, the norm detects units over any commutative base ring. -/
theorem isUnit_norm_iff (s : S) : IsUnit (Algebra.norm R s) ↔ IsUnit s := by
  let _ := Fintype.ofFinite ι
  let _ := Module.Free.of_basis b
  let _ := Module.Finite.of_basis b
  rw [Algebra.norm_apply, ← LinearMap.isUnit_iff_isUnit_det, Algebra.lmul_isUnit_iff]

variable (T : Type*) [CommRing T] [Algebra R T]

omit [Finite ι] in
/-- The multiplication matrix on the scalar extension is the original matrix mapped entrywise. -/
theorem leftMulMatrix_baseChange [Fintype ι] [DecidableEq ι] (s : S) :
    Algebra.leftMulMatrix (b.baseChange T) (1 ⊗ₜ[R] s) =
      (algebraMap R T).mapMatrix (Algebra.leftMulMatrix b s) := by
  ext i j
  simp only [Algebra.leftMulMatrix_eq_repr_mul, Basis.baseChange_apply,
    Algebra.TensorProduct.tmul_mul_tmul, Basis.baseChange_repr_tmul,
    Algebra.smul_def, mul_one, RingHom.mapMatrix_apply, Matrix.map_apply]

/-- A genuine finite-free norm commutes with arbitrary, possibly nonflat scalar extension. -/
theorem norm_baseChange (s : S) :
    Algebra.norm T (1 ⊗ₜ[R] s : T ⊗[R] S) = algebraMap R T (Algebra.norm R s) := by
  classical
  let _ := Fintype.ofFinite ι
  rw [Algebra.norm_eq_matrix_det (b.baseChange T), Algebra.norm_eq_matrix_det b,
    leftMulMatrix_baseChange, RingHom.map_det]

/-- Nonvanishing in a field is equivalent to invertibility of the full scalar-extended element. -/
theorem norm_ne_zero_iff {K : Type*} [Field K] [Algebra R K] (s : S) :
    algebraMap R K (Algebra.norm R s) ≠ 0 ↔ IsUnit (1 ⊗ₜ[R] s : K ⊗[R] S) := by
  rw [← norm_baseChange b K, ← isUnit_iff_ne_zero]
  exact isUnit_norm_iff (b.baseChange K) _

/-- The base-changed norm is unchanged by a linear algebra equivalence of the whole envelope. -/
theorem norm_baseChange_equiv {C : Type*} [CommRing C] [Algebra T C]
    (e : (T ⊗[R] S) ≃ₐ[T] C) (s : S) :
    Algebra.norm T (e (1 ⊗ₜ[R] s)) = algebraMap R T (Algebra.norm R s) := by
  rw [Algebra.norm_eq_of_algEquiv, norm_baseChange b T]

end FLT.Mazur.FiniteFreeTranslationNorm
