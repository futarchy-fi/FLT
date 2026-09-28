/-
Copyright (c) 2026 krandder. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: krandder
-/
module

public import FLT.GroupScheme.HenselianIdempotents
public import Mathlib.LinearAlgebra.TensorProduct.RightExactness
public import Mathlib.RingTheory.Ideal.GoingUp
public import Mathlib.RingTheory.TensorProduct.Finite

/-!
# Tensor products of pointed local algebras

If a local algebra has a point over the base, tensoring it with a finite
connected algebra preserves connectedness. The point's kernel lies in the
Jacobson radical, and this remains true after the finite base change.
-/

@[expose] public noncomputable section

open scoped TensorProduct

namespace ThreeAdicPlan

/-- Integral homomorphisms carry the Jacobson radical into the Jacobson radical. -/
theorem map_jacobson_le_of_isIntegral {A B : Type*} [CommRing A] [CommRing B]
    (f : A →+* B) (hf : f.IsIntegral) :
    ((⊥ : Ideal A).jacobson).map f ≤ (⊥ : Ideal B).jacobson := by
  rw [Ideal.map_le_iff_le_comap]
  intro x hx
  rw [Ideal.mem_comap, Ideal.jacobson, Ideal.mem_sInf]
  rintro m ⟨_, hm⟩
  let := hm
  have hmc := Ideal.isMaximal_comap_of_isIntegral_of_isMaximal f hf m
  exact (Ideal.mem_sInf.mp hx) ⟨bot_le, hmc⟩

/-- A homomorphism whose kernel lies in the Jacobson radical detects idempotents. -/
theorem idempotent_eq_of_map_eq {A B : Type*} [CommRing A] [CommRing B]
    (f : A →+* B) (hf : RingHom.ker f ≤ (⊥ : Ideal A).jacobson)
    {e d : A} (he : IsIdempotentElem e) (hd : IsIdempotentElem d)
    (h : f e = f d) : e = d := by
  apply idempotent_eq_of_quotient_eq (RingHom.ker f) hf he hd
  rw [Ideal.Quotient.eq, RingHom.mem_ker, map_sub, h, sub_self]

/-- A pointed local algebra tensored with a finite connected algebra is connected. -/
theorem tensor_idempotent_trivial_of_local_point
    {R A B : Type*} [CommRing R] [Nontrivial R] [CommRing A] [CommRing B]
    [Algebra R A] [Algebra R B] [IsLocalRing A] [Module.Finite R B]
    (ε : A →ₐ[R] R) (hc : ∀ d : B, IsIdempotentElem d → d = 0 ∨ d = 1)
    (d : A ⊗[R] B) (hd : IsIdempotentElem d) : d = 0 ∨ d = 1 := by
  let f := Algebra.TensorProduct.map ε (AlgHom.id R B)
  have hε : Function.Surjective ε := fun r ↦ ⟨algebraMap R A r, ε.commutes r⟩
  have hker : RingHom.ker f.toRingHom ≤ (⊥ : Ideal (A ⊗[R] B)).jacobson := by
    change RingHom.ker (Algebra.TensorProduct.map ε (AlgHom.id R B)) ≤ _
    rw [Algebra.TensorProduct.rTensor_ker ε hε]
    have hloc : RingHom.ker ε ≤ (⊥ : Ideal A).jacobson := by
      rw [IsLocalRing.jacobson_eq_maximalIdeal _ bot_ne_top]
      exact IsLocalRing.le_maximalIdeal (RingHom.ker_ne_top ε)
    apply (Ideal.map_mono hloc).trans
    exact map_jacobson_le_of_isIntegral (algebraMap A (A ⊗[R] B))
      (algebraMap_isIntegral_iff.mpr inferInstance)
  let E := Algebra.TensorProduct.lid R B
  rcases hc (E (f d)) ((hd.map f.toRingHom).map E.toRingEquiv.toRingHom) with h | h
  · left
    apply idempotent_eq_of_map_eq f.toRingHom hker hd .zero
    apply E.injective
    change E (f d) = E (f 0)
    simpa only [map_zero] using h
  · right
    apply idempotent_eq_of_map_eq f.toRingHom hker hd .one
    apply E.injective
    change E (f d) = E (f 1)
    simpa only [map_one] using h

end ThreeAdicPlan
