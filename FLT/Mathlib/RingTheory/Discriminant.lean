/-
Copyright (c) 2026 krandder. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: krandder
-/
module

public import Mathlib.RingTheory.Discriminant
public import Mathlib.RingTheory.Etale.Field
public import Mathlib.FieldTheory.IsAlgClosed.AlgebraicClosure
public import Mathlib.LinearAlgebra.TensorProduct.Basis

/-!
# Discriminants of finite étale algebras

Discriminants commute with scalar extension. A finite étale algebra over a field
has nonzero discriminant in every basis, including when the algebra is a product
of fields. The proof splits the algebra over an algebraic closure.
-/

@[expose] public noncomputable section

open scoped TensorProduct

namespace Algebra

variable {R S A ι : Type*} [CommRing R] [CommRing S] [CommRing A]
  [Algebra R S] [Algebra R A]

/-- The trace of an integral tensor is obtained by extending the original trace. -/
theorem trace_includeRight_of_basis [Finite ι] (b : Module.Basis ι R A) (x : A) :
    trace S (S ⊗[R] A) (1 ⊗ₜ[R] x) = algebraMap R S (trace R A x) := by
  classical
  let := Fintype.ofFinite ι
  rw [trace_eq_matrix_trace (b.baseChange S), trace_eq_matrix_trace b]
  simp [Matrix.trace, leftMulMatrix_eq_repr_mul, Algebra.TensorProduct.tmul_mul_tmul,
    Algebra.algebraMap_eq_smul_one]

/-- Extending the coefficient ring extends the discriminant of a basis. -/
theorem discr_baseChange [Fintype ι] [DecidableEq ι] (b : Module.Basis ι R A) :
    discr S (b.baseChange S) = algebraMap R S (discr R b) := by
  rw [discr_def, discr_def, RingHom.map_det]
  congr 1
  ext i j
  simp only [traceMatrix_apply, traceForm_apply, Module.Basis.baseChange_apply,
    RingHom.mapMatrix_apply, Matrix.map_apply]
  rw [Algebra.TensorProduct.tmul_mul_tmul, one_mul, trace_includeRight_of_basis b]

/-- The trace on a finite product of copies of the base ring is the sum of coordinates. -/
theorem trace_pi_apply (R ι : Type*) [CommRing R] [Fintype ι] (x : ι → R) :
    trace R (ι → R) x = ∑ i, x i := by
  classical
  rw [trace_eq_matrix_trace (Pi.basisFun R ι)]
  simp [Matrix.trace, leftMulMatrix_eq_repr_mul, Pi.basisFun_apply]

/-- The trace pairing of a split finite algebra is nondegenerate. -/
theorem traceForm_nondegenerate_pi (R ι : Type*) [CommRing R] [Finite ι] :
    (traceForm R (ι → R)).Nondegenerate := by
  classical
  let := Fintype.ofFinite ι
  have hleft : ∀ x : ι → R, (∀ y, traceForm R (ι → R) x y = 0) → x = 0 := by
    intro x hx
    ext i
    simpa [traceForm_apply, trace_pi_apply, Pi.mul_apply, Pi.single_apply] using
      hx (Pi.single i 1)
  exact ⟨hleft, fun x hx ↦ hleft x (fun y ↦ by simpa [traceForm_apply, mul_comm] using hx y)⟩

/-- The trace pairing of a finite étale algebra over a separably closed field is nondegenerate. -/
theorem traceForm_nondegenerate_of_isSepClosed (K A : Type*) [Field K] [CommRing A]
    [Algebra K A] [Etale K A] [IsSepClosed K] : (traceForm K A).Nondegenerate := by
  let : Module.Finite K A := Algebra.FormallyUnramified.finite_of_free K A
  let : IsArtinianRing A := isArtinian_of_tower K inferInstance
  let := Fintype.ofFinite (PrimeSpectrum A)
  let e := Algebra.FormallyEtale.equivPiOfIsSepClosed K A
  have hleft : ∀ x : A, (∀ y, traceForm K A x y = 0) → x = 0 := by
    intro x hx
    apply e.injective
    rw [map_zero]
    apply (traceForm_nondegenerate_pi K (PrimeSpectrum A)).1
    intro y
    obtain ⟨z, rfl⟩ := e.surjective y
    simpa only [traceForm_apply, ← map_mul, trace_eq_of_algEquiv] using hx z
  exact ⟨hleft, fun x hx ↦ hleft x (fun y ↦ by simpa [traceForm_apply, mul_comm] using hx y)⟩

/-- Every basis of a finite étale algebra over a field has nonzero discriminant.
The algebra need not itself be a field. -/
theorem discr_ne_zero_of_etale {K A ι : Type*} [Field K] [CommRing A] [Algebra K A]
    [Etale K A] [Fintype ι] [DecidableEq ι] (b : Module.Basis ι K A) :
    discr K b ≠ 0 := by
  let L := AlgebraicClosure K
  have hne : discr L (b.baseChange L) ≠ 0 := by
    rw [discr_def, traceMatrix_of_basis,
      ← LinearMap.BilinForm.nondegenerate_iff_det_ne_zero]
    exact traceForm_nondegenerate_of_isSepClosed L (L ⊗[K] A)
  rw [discr_baseChange] at hne
  exact fun h ↦ hne (by rw [h, map_zero])

end Algebra
