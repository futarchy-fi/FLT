/-
Copyright (c) 2026 krandder. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: krandder
-/
module

public import Mathlib.RingTheory.Ideal.Quotient.Operations

/-! # Rigidity near an augmentation with idempotent kernel -/

@[expose] public section
namespace AlgHom
variable {R A B : Type*} [CommRing R] [CommRing A] [CommRing B]
  [Algebra R A] [Algebra R B]

/-- An augmentation with idempotent kernel has no nontrivial square-zero perturbations. -/
theorem eq_augmentation_of_idempotent_ker (ε : A →ₐ[R] R)
    (hε : IsIdempotentElem (RingHom.ker ε.toRingHom)) (I : Ideal B) (hI : I ^ 2 = ⊥)
    (f : A →ₐ[R] B) (hf : (Ideal.Quotient.mkₐ R I).comp f =
      (Ideal.Quotient.mkₐ R I).comp ((Algebra.ofId R B).comp ε)) :
    f = (Algebra.ofId R B).comp ε := by
  let J := RingHom.ker ε.toRingHom
  have hJI : J.map f.toRingHom ≤ I := by
    apply Ideal.map_le_iff_le_comap.mpr
    intro a ha
    change f a ∈ I
    apply Ideal.Quotient.eq_zero_iff_mem.mp
    change (Ideal.Quotient.mkₐ R I) (f a) = 0
    have h := AlgHom.congr_fun hf a
    change ε a = 0 at ha
    simpa only [AlgHom.comp_apply, Algebra.ofId_apply, ha, map_zero] using h
  have hJzero : J.map f.toRingHom = ⊥ := by
    apply bot_unique
    calc
      J.map f.toRingHom = (J.map f.toRingHom) * (J.map f.toRingHom) := by
        rw [← Ideal.map_mul, hε.eq]
      _ ≤ I * I := mul_le_mul' hJI hJI
      _ = ⊥ := by rw [← pow_two, hI]
  ext a
  have ha : a - algebraMap R A (ε a) ∈ J := by
    change ε (a - algebraMap R A (ε a)) = 0
    simp
  have hz := Ideal.mem_map_of_mem f.toRingHom ha
  rw [hJzero, Ideal.mem_bot] at hz
  change f (a - algebraMap R A (ε a)) = 0 at hz
  rw [map_sub, f.commutes, sub_eq_zero] at hz
  exact hz
end AlgHom
