/-
Copyright (c) 2026 krandder. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: krandder
-/
module

public import Mathlib.NumberTheory.Padics.RingHoms
public import Mathlib.RingTheory.TensorProduct.Quotient

/-! # Principal reduction and the special fibre of a p-adic algebra -/

@[expose] public noncomputable section

open scoped TensorProduct

namespace PadicInt

variable (p : ℕ) [Fact p.Prime]

/-- The residue field is an algebra over the p-adic integers via reduction. -/
instance instAlgebraZMod : Algebra ℤ_[p] (ZMod p) := toZMod.toAlgebra

/-- Reduction of the p-adic integers is the canonical residue algebra map. -/
@[simp] theorem algebraMap_zmod : algebraMap ℤ_[p] (ZMod p) = toZMod := rfl

/-- The principal residue quotient of the p-adic integers is the prime field. -/
def modPEquivZMod : (ℤ_[p] ⧸ Ideal.span {(p : ℤ_[p])}) ≃ₐ[ℤ_[p]] ZMod p :=
  (Ideal.quotientEquivAlgOfEq ℤ_[p]
    (ker_toZMod.trans maximalIdeal_eq_span_p).symm).trans
    (Ideal.quotientKerAlgEquivOfSurjective
      (f := Algebra.ofId ℤ_[p] (ZMod p)) (ZMod.ringHom_surjective toZMod))

/-- The residue quotient equivalence agrees with reduction on p-adic integers. -/
@[simp] theorem modPEquivZMod_mk (x : ℤ_[p]) :
    modPEquivZMod p (Ideal.Quotient.mk _ x) = toZMod x := rfl

variable (A : Type*) [CommRing A] [Algebra ℤ_[p] A]

/-- The principal reduction of a p-adic algebra is its base change to the residue field. -/
def modPEquivSpecialFiber :
    (A ⧸ Ideal.span {algebraMap ℤ_[p] A (p : ℤ_[p])}) ≃ₐ[ℤ_[p]]
      (ZMod p) ⊗[ℤ_[p]] A := by
  let I : Ideal ℤ_[p] := Ideal.span {(p : ℤ_[p])}
  let e : (A ⧸ I.map (algebraMap ℤ_[p] A)) ≃ₐ[ℤ_[p]] (ℤ_[p] ⧸ I) ⊗[ℤ_[p]] A :=
    { __ := (Algebra.TensorProduct.quotIdealMapEquivQuotTensor A I).toRingEquiv
      commutes' r := by
        change (1 : ℤ_[p] ⧸ I) ⊗ₜ[ℤ_[p]] (algebraMap ℤ_[p] A r) =
          algebraMap ℤ_[p] ((ℤ_[p] ⧸ I) ⊗[ℤ_[p]] A) r
        exact (Algebra.TensorProduct.tmul_one_eq_one_tmul (R := ℤ_[p])
          (A := ℤ_[p] ⧸ I) (B := A) r).symm }
  exact (Ideal.quotientEquivAlgOfEq ℤ_[p] (by
    rw [Ideal.map_span, Set.image_singleton])).trans
    (e.trans (Algebra.TensorProduct.congr (modPEquivZMod p) (AlgEquiv.refl : A ≃ₐ[ℤ_[p]] A)))

/-- The special-fibre comparison sends a reduced coordinate to its base change. -/
@[simp] theorem modPEquivSpecialFiber_mk (a : A) :
    modPEquivSpecialFiber p A (Ideal.Quotient.mk _ a) = 1 ⊗ₜ[ℤ_[p]] a := by
  simp [modPEquivSpecialFiber, Algebra.TensorProduct.congr_apply]

end PadicInt
