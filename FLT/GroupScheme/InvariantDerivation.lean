/-
Copyright (c) 2026 krandder. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: krandder
-/
module

public import Mathlib.RingTheory.Bialgebra.TensorProduct
public import Mathlib.RingTheory.Derivation.Basic
public import Mathlib.RingTheory.Ideal.Cotangent
public import Mathlib.Tactic.Ring

/-!
# Invariant extensions of tangent vectors

A linear functional satisfying the Leibniz rule at the counit of a commutative
bialgebra extends to an algebra-valued derivation by comultiplication.
Evaluating the extension at the counit recovers the original tangent vector.
-/

@[expose] public noncomputable section

open scoped TensorProduct

namespace Bialgebra

variable {k A : Type*} [CommRing k] [CommRing A] [Bialgebra k A]

/-- Extend a scalar-valued linear map by applying it to the right tensor factor
of comultiplication. -/
def invariantLinearMap (d : A →ₗ[k] k) : A →ₗ[k] A :=
  (_root_.TensorProduct.rid k A).toLinearMap ∘ₗ
    _root_.TensorProduct.map LinearMap.id d ∘ₗ Coalgebra.comul

/-- A finite tensor expression for the invariant extension. -/
theorem invariantLinearMap_apply (d : A →ₗ[k] k) {a : A} {ι : Type*}
    (r : Coalgebra.Repr k a ι) :
    invariantLinearMap d a = ∑ i ∈ r.index, d (r.right i) • r.left i := by
  simp only [invariantLinearMap, LinearMap.comp_apply, ← r.eq, map_sum,
    _root_.TensorProduct.map_tmul, LinearMap.id_apply, LinearEquiv.coe_coe,
    _root_.TensorProduct.rid_tmul]

/-- The counit of an invariant extension recovers the scalar linear map. -/
theorem counit_invariantLinearMap (d : A →ₗ[k] k) (a : A) :
    Coalgebra.counit (R := k) (invariantLinearMap d a) = d a := by
  let r := Coalgebra.Repr.arbitrary k a
  rw [invariantLinearMap_apply d r]
  have h := congrArg d (Coalgebra.sum_counit_smul r)
  simpa only [map_sum, map_smul, smul_eq_mul, mul_comm] using h

/-- Applying the counit on the right factor of a coproduct recovers the element. -/
theorem sum_right_counit_smul {a : A} {ι : Type*} (r : Coalgebra.Repr k a ι) :
    ∑ i ∈ r.index, Coalgebra.counit (R := k) (r.right i) • r.left i = a := by
  simpa only [map_sum, _root_.TensorProduct.rid_tmul, one_smul] using
    congrArg (_root_.TensorProduct.rid k A) (Coalgebra.sum_tmul_counit_eq r)

/-- The invariant extension of a tangent vector satisfies the algebra Leibniz rule. -/
theorem invariantLinearMap_leibniz (d : A →ₗ[k] k)
    (hd : ∀ a b, d (a * b) = Coalgebra.counit (R := k) a * d b +
      Coalgebra.counit (R := k) b * d a) (a b : A) :
    invariantLinearMap d (a * b) =
      a * invariantLinearMap d b + b * invariantLinearMap d a := by
  let r := Coalgebra.Repr.arbitrary k a
  let s := Coalgebra.Repr.arbitrary k b
  rw [invariantLinearMap_apply d (r.mul s), invariantLinearMap_apply d r,
    invariantLinearMap_apply d s]
  simp only [Coalgebra.Repr.mul_index, Coalgebra.Repr.mul_left, Coalgebra.Repr.mul_right,
    Finset.sum_product, hd, add_smul, Finset.sum_add_distrib]
  have hterm (i j : A × A) :
      (Coalgebra.counit (R := k) (r.right i) * d (s.right j)) •
          (r.left i * s.left j) =
        (Coalgebra.counit (R := k) (r.right i) • r.left i) *
          (d (s.right j) • s.left j) := by
    simp only [Algebra.smul_def, map_mul]
    ring
  have hterm' (i j : A × A) :
      (Coalgebra.counit (R := k) (s.right j) * d (r.right i)) •
          (r.left i * s.left j) =
        (d (r.right i) • r.left i) *
          (Coalgebra.counit (R := k) (s.right j) • s.left j) := by
    simp only [Algebra.smul_def, map_mul]
    ring
  simp only [hterm, hterm', ← Finset.mul_sum, ← Finset.sum_mul,
    sum_right_counit_smul]
  ring

/-- A tangent vector at the counit extends to an algebra-valued derivation. -/
def invariantDerivation (d : A →ₗ[k] k) (h1 : d 1 = 0)
    (hd : ∀ a b, d (a * b) = Coalgebra.counit (R := k) a * d b +
      Coalgebra.counit (R := k) b * d a) : Derivation k A A where
  __ := invariantLinearMap d
  map_one_eq_zero' := by
    simp [invariantLinearMap, Bialgebra.comul_one, Algebra.TensorProduct.one_def, h1]
  leibniz' a b := invariantLinearMap_leibniz d hd a b

/-- The constructed derivation has the prescribed tangent vector. -/
theorem counit_invariantDerivation (d : A →ₗ[k] k) (h1 : d 1 = 0)
    (hd : ∀ a b, d (a * b) = Coalgebra.counit (R := k) a * d b +
      Coalgebra.counit (R := k) b * d a) (a : A) :
    Coalgebra.counit (R := k) (invariantDerivation d h1 hd a) = d a :=
  counit_invariantLinearMap d a

end Bialgebra
