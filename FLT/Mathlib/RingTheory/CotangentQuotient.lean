/-
Copyright (c) 2026 krandder. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: krandder
-/
module

public import Mathlib.RingTheory.Ideal.Cotangent
public import Mathlib.RingTheory.Ideal.Quotient.Operations

/-!
# Cotangent spaces after quotienting by quadratic relations

Quotienting by an ideal contained in `I²` preserves the cotangent module of
`I`. This makes precise that Frobenius powers introduce no new tangent-space
relations.
-/

@[expose] public noncomputable section

namespace Ideal

variable {A : Type*} [CommRing A]

/-- Quotienting by relations in `I²` preserves the cotangent module of `I`. -/
def cotangentQuotientEquiv (I J : Ideal A) (hJ : J ≤ I ^ 2) :
    I.Cotangent ≃ₗ[A] (I.map (Ideal.Quotient.mk J)).Cotangent := by
  let B := A ⧸ J
  let K := I.map (algebraMap A B)
  have hsurj : Function.Surjective (algebraMap A B) := Ideal.Quotient.mk_surjective
  have hc : K.comap (algebraMap A B) = RingHom.ker (algebraMap A B) ⊔ I := by
    rw [Ideal.comap_map_of_surjective _ hsurj, sup_comm]
    rfl
  let f := Ideal.mapCotangent I K (Algebra.ofId A B)
    (le_of_le_of_eq le_sup_right hc.symm)
  have hf : Function.Surjective f := Ideal.mapCotangent_surjective_of_comap_eq hsurj hc
  have hinj : Function.Injective f := by
    rw [← LinearMap.ker_eq_bot]
    change (Ideal.mapCotangent I K (Algebra.ofId A B) _).ker = ⊥
    rw [Ideal.mapCotangent_ker_of_surjective hsurj hc]
    apply le_bot_iff.mp
    rintro y ⟨x, hx, rfl⟩
    change I.toCotangent x = 0
    apply (I.toCotangent_eq_zero x).mpr
    apply hJ
    change (x : A) ∈ RingHom.ker (algebraMap A B) ⊓ I at hx
    have hker : RingHom.ker (algebraMap A B) = J := Ideal.mk_ker
    rw [hker] at hx
    exact hx.1
  exact LinearEquiv.ofBijective f ⟨hinj, hf⟩

/-- The cotangent dimension is unchanged by quotienting by quadratic relations. -/
theorem finrank_cotangent_map_quotient (k : Type*) [Field k] [Algebra k A]
    (I J : Ideal A) (hJ : J ≤ I ^ 2) :
    Module.finrank k (I.map (Ideal.Quotient.mk J)).Cotangent =
      Module.finrank k I.Cotangent :=
  ((I.cotangentQuotientEquiv J hJ).restrictScalars k).finrank_eq.symm

end Ideal
