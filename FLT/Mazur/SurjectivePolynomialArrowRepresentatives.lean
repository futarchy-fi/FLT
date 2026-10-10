/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.PrincipalQuotientRepresentatives

/-!
# Polynomial representatives through an arbitrary surjective algebra map

Lift an actual principal-open arrow through any surjective target presentation.
The kernel records both relation preservation and a chosen inverse equation.
-/

@[expose] public noncomputable section

namespace FLT.Mazur.PrincipalQuotientProjection

universe u v w

variable {R : Type u} [CommRing R] (n : ℕ)
  (I : Ideal (MvPolynomial (Fin n) R)) (a : MvPolynomial (Fin n) R)
  {S : Type v} [CommRing S] [Algebra R S]
  {T : Type w} [CommRing T] [Algebra R T]

/-- A surjective target presentation lifts all polynomial images and inverse data. -/
theorem exists_representatives_of_surjective (q : S →ₐ[R] T)
    (hq : Function.Surjective q) (F : Target I a →ₐ[R] T) :
    ∃ f : MvPolynomial (Fin n) R →ₐ[R] S,
      (∀ p, q (f p) = F (algebraMap _ (Target I a) (Ideal.Quotient.mk I p))) ∧
      I ≤ (RingHom.ker q.toRingHom).comap f.toRingHom ∧
      ∃ v : S, f a * v - 1 ∈ RingHom.ker q.toRingHom := by
  let g : MvPolynomial (Fin n) R →ₐ[R] Target I a :=
    (IsScalarTower.toAlgHom R (MvPolynomial (Fin n) R ⧸ I) (Target I a)).comp
      (Ideal.Quotient.mkₐ R I)
  choose y hy using fun k : Fin n ↦ hq (F (g (MvPolynomial.X k)))
  let f : MvPolynomial (Fin n) R →ₐ[R] S := MvPolynomial.aeval y
  have hfg : q.comp f = F.comp g := by
    apply MvPolynomial.algHom_ext
    intro k
    change q (MvPolynomial.aeval y (MvPolynomial.X k)) = _
    rw [MvPolynomial.aeval_X]
    exact hy k
  have hfac (p) : q (f p) =
      F (algebraMap _ (Target I a) (Ideal.Quotient.mk I p)) := AlgHom.congr_fun hfg p
  refine ⟨f, hfac, ?_, ?_⟩
  · intro p hp
    change q (f p) = 0
    rw [hfac, Ideal.Quotient.eq_zero_iff_mem.mpr hp, map_zero, map_zero]
  · obtain ⟨v, hv⟩ := hq
      (F (IsLocalization.Away.invSelf (S := Target I a) (Ideal.Quotient.mk I a)))
    refine ⟨v, ?_⟩
    change q (f a * v - 1) = 0
    rw [map_sub, map_mul, map_one, hfac, hv, ← map_mul,
      IsLocalization.Away.mul_invSelf, map_one, sub_self]

end FLT.Mazur.PrincipalQuotientProjection
