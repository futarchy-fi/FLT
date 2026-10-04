/-
Copyright (c) 2026 krandder. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: krandder
-/
module

public import Mathlib.RingTheory.TensorProduct.MvPolynomial
public import Mathlib.RingTheory.TensorProduct.Quotient

/-! # Exact reconstruction of polynomial relation quotients under base change -/

@[expose] public noncomputable section

open scoped TensorProduct
open Algebra.TensorProduct

namespace MvPolynomial

variable {R S σ ι : Type*} [CommRing R] [CommRing S] [Algebra R S]

/-- A quotient by specified polynomial relations commutes with arbitrary coefficient
base change, without a flatness assumption. -/
def relationBaseChangeEquiv (g : ι → MvPolynomial σ R) :
    (S ⊗[R] (MvPolynomial σ R ⧸ Ideal.span (Set.range g))) ≃ₐ[S]
      (MvPolynomial σ S ⧸ Ideal.span (Set.range fun i ↦ map (algebraMap R S) (g i))) := by
  let I := Ideal.span (Set.range g)
  let e := algebraTensorAlgEquiv (σ := σ) R S
  have hc : e.toRingHom.comp (includeRight : MvPolynomial σ R →ₐ[R]
      S ⊗[R] MvPolynomial σ R).toRingHom = map (algebraMap R S) := by
    apply RingHom.ext
    intro q
    simp [e]
  refine (tensorQuotientEquiv S (MvPolynomial σ R) S I).trans
    (Ideal.quotientEquivAlg _ _ e ?_)
  change Ideal.span (Set.range fun i ↦ map (algebraMap R S) (g i)) =
    (I.map (includeRight : MvPolynomial σ R →ₐ[R] S ⊗[R] MvPolynomial σ R).toRingHom).map
      e.toRingHom
  rw [Ideal.map_map, hc, Ideal.map_span, ← Set.range_comp]
  rfl

/-- Reconstruction preserves the original polynomial representatives. -/
@[simp] theorem relationBaseChangeEquiv_one_tmul_mk (g : ι → MvPolynomial σ R)
    (q : MvPolynomial σ R) :
    relationBaseChangeEquiv (S := S) g (1 ⊗ₜ[R] Ideal.Quotient.mk _ q) =
      Ideal.Quotient.mk _ (map (algebraMap R S) q) := by
  simp [relationBaseChangeEquiv]

end MvPolynomial
