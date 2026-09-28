/-
Copyright (c) 2026 krandder. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: krandder
-/
module

public import FLT.Mathlib.RingTheory.MvPolynomial.CoefficientKernel
public import FLT.Mathlib.RingTheory.NilpotentRelationLifting

/-!
# Lifting a pure-power polynomial presentation

A projective algebra over a nilpotent augmented base inherits a presentation
by the expected deformed pure-power equations when its reduced kernel is
known. This is the relative presentation step in Frobenius induction.
-/

@[expose] public noncomputable section

namespace MvPolynomial

variable {k R A B ι : Type*} [CommRing k] [CommRing R] [CommRing A] [CommRing B]
  [Algebra k R] [Algebra k A] [Algebra R A] [Algebra k B]
  [Module.Projective R A]

/-- Pure-power relations of the special fibre lift to deformed pure-power
relations over a nilpotent augmented base. -/
theorem ker_aeval_eq_span_of_nilpotent_reduction
    (ε : R →ₐ[k] k) (hε : IsNilpotent (RingHom.ker ε))
    (q : A →ₐ[k] B)
    (hq : ∀ r, q (algebraMap R A r) = algebraMap k B (ε r))
    (x : ι → A) (hx : Function.Surjective (aeval (R := R) x))
    (p : ℕ) (z : ι → R) (hz : ∀ i, ε (z i) = 0)
    (hpow : ∀ i, x i ^ p = algebraMap R A (z i))
    (hker : RingHom.ker (aeval (R := k) (fun i ↦ q (x i))) =
      Ideal.span (Set.range (fun i ↦ (X i : MvPolynomial ι k) ^ p))) :
    RingHom.ker (aeval (R := R) x) =
      Ideal.span (Set.range (fun i ↦ (X i : MvPolynomial ι R) ^ p - C (z i))) := by
  classical
  let J : Ideal (MvPolynomial ι R) :=
    Ideal.span (Set.range (fun i ↦ (X i : MvPolynomial ι R) ^ p - C (z i)))
  let m := map (σ := ι) ε.toRingHom
  have hdiag : q.toRingHom.comp (aeval (R := R) x).toRingHom =
      (aeval (R := k) (fun i ↦ q (x i))).toRingHom.comp m := by
    apply ringHom_ext
    · intro r
      simpa [m] using hq r
    · intro i
      simp [m]
  have hmap : J.map m = RingHom.ker (aeval (R := k) (fun i ↦ q (x i))) := by
    rw [hker]
    simp only [J, Ideal.map_span, ← Set.range_comp, Function.comp_def,
      m, map_sub, map_pow, map_X, map_C, show ∀ i, ε.toRingHom (z i) = 0 from hz,
      map_zero, sub_zero]
  have hm : Function.Surjective m := map_surjective _ (fun a ↦ ⟨algebraMap k R a, ε.commutes a⟩)
  apply (aeval (R := R) x).ker_eq_of_le_sup_map_of_isNilpotent hx hε
  · apply Ideal.span_le.mpr
    rintro _ ⟨i, rfl⟩
    change aeval x ((X i) ^ p - C (z i)) = 0
    simp only [map_sub, map_pow, aeval_X, aeval_C, hpow, sub_self]
  · intro f hf
    have hfm : m f ∈ J.map m := by
      rw [hmap]
      change aeval (fun i ↦ q (x i)) (m f) = 0
      have he := DFunLike.congr_fun hdiag f
      change q (aeval (R := R) x f) = aeval (fun i ↦ q (x i)) (m f) at he
      rw [← he, show aeval (R := R) x f = 0 from hf, map_zero]
    have hc : f ∈ (J.map m).comap m := hfm
    rw [Ideal.comap_map_of_surjective _ hm] at hc
    change f ∈ J ⊔ RingHom.ker (map ε.toRingHom) at hc
    rw [ker_map_eq_map_C] at hc
    exact hc

end MvPolynomial
