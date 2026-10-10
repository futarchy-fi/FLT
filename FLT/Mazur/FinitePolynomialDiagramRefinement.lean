/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.FinitePolynomialStableStages

/-!
# Cofinal refinement retaining every old finite diagram arrow

Lift the old arrows to polynomial maps, then close their relation ideals
simultaneously. Sources and targets advance together, and every old arrow
square commutes on its entire finite-stage source ring.
-/

@[expose] public noncomputable section

namespace FLT.Mazur.FinitePolynomialCoefficients

universe u v w z

variable {R : Type u} [CommRing R]

/-- Polynomial maps lift along any surjective algebra map by lifting generators. -/
theorem exists_polynomial_lift {A : Type v} [CommRing A] [Algebra R A]
    {B : Type w} [CommRing B] [Algebra R B] (π : A →ₐ[R] B)
    (hπ : Function.Surjective π) {σ : Type z} (f : MvPolynomial σ R →ₐ[R] B) :
    ∃ g : MvPolynomial σ R →ₐ[R] A, π.comp g = f := by
  choose x hx using fun i ↦ hπ (f (MvPolynomial.X i))
  refine ⟨MvPolynomial.aeval x, ?_⟩
  apply MvPolynomial.algHom_ext
  intro i
  simpa only [AlgHom.comp_apply, MvPolynomial.aeval_X] using hx i

variable {ι : Type v} [Finite ι] {E : Type w} [Finite E]
  (n : ι → ℕ) (src dst : E → ι)
  (I : ∀ i, Ideal (MvPolynomial (Fin (n i)) R))

/-- Prescribed finite diagram arrows survive a simultaneous cofinal refinement. -/
theorem exists_diagram_refinement (s b : ∀ i, Finset (I i))
    (g : ∀ e, FiniteRelationModel.Stage (I (src e)) (s (src e)) →ₐ[R]
      FiniteRelationModel.Stage (I (dst e)) (s (dst e)))
    (f : ∀ e, (MvPolynomial (Fin (n (src e))) R ⧸ I (src e)) →ₐ[R]
      (MvPolynomial (Fin (n (dst e))) R ⧸ I (dst e)))
    (hfac : ∀ e, (FiniteRelationModel.toQuotient R (I (dst e)) (s (dst e))).comp (g e) =
      (f e).comp (FiniteRelationModel.toQuotient R (I (src e)) (s (src e)))) :
    ∃ (t : ∀ i, Finset (I i)) (hst : s ≤ t), b ≤ t ∧
      ∃ k : ∀ e, FiniteRelationModel.Stage (I (src e)) (t (src e)) →ₐ[R]
        FiniteRelationModel.Stage (I (dst e)) (t (dst e)),
        (∀ e, (k e).comp (FiniteRelationModel.transition R (I (src e)) (hst (src e))) =
          (FiniteRelationModel.transition R (I (dst e)) (hst (dst e))).comp (g e)) ∧
        ∀ e, (FiniteRelationModel.toQuotient R (I (dst e)) (t (dst e))).comp (k e) =
          (f e).comp (FiniteRelationModel.toQuotient R (I (src e)) (t (src e))) := by
  choose p hp using fun e ↦ exists_polynomial_lift
    (Ideal.Quotient.mkₐ R (FiniteRelationModel.relations (I (dst e)) (s (dst e))))
    (Ideal.Quotient.mkₐ_surjective R _)
    ((g e).comp (Ideal.Quotient.mkₐ R
      (FiniteRelationModel.relations (I (src e)) (s (src e)))))
  have hproj (e) : (Ideal.Quotient.mkₐ R (I (dst e))).comp (p e) =
      (f e).comp (Ideal.Quotient.mkₐ R (I (src e))) := by
    have h := congrArg (fun a ↦
      (FiniteRelationModel.toQuotient R (I (dst e)) (s (dst e))).comp a) (hp e)
    simp only [← AlgHom.comp_assoc] at h
    rw [hfac] at h
    exact h
  have hI (e) : I (src e) ≤ (I (dst e)).comap (p e).toRingHom := by
    intro x hx
    change p e x ∈ I (dst e)
    apply Ideal.Quotient.eq_zero_iff_mem.mp
    change Ideal.Quotient.mk (I (dst e)) (p e x) = 0
    have h := AlgHom.congr_fun (hproj e) x
    change Ideal.Quotient.mk (I (dst e)) (p e x) =
      f e (Ideal.Quotient.mk (I (src e)) x) at h
    rw [h, Ideal.Quotient.eq_zero_iff_mem.mpr hx, map_zero]
  classical
  obtain ⟨t, ht, hrel⟩ := exists_stable_stages n src dst p I hI (fun i ↦ s i ∪ b i)
  have hst : s ≤ t := fun i ↦ Finset.subset_union_left.trans (ht i)
  let k (e) := Ideal.quotientMapₐ (FiniteRelationModel.relations (I (dst e)) (t (dst e)))
    (p e) (hrel e)
  have hcomm (e) : (k e).comp (FiniteRelationModel.transition R (I (src e)) (hst (src e))) =
      (FiniteRelationModel.transition R (I (dst e)) (hst (dst e))).comp (g e) := by
    apply (AlgHom.cancel_right (Ideal.Quotient.mkₐ_surjective R
      (FiniteRelationModel.relations (I (src e)) (s (src e))))).mp
    apply AlgHom.ext
    intro x
    exact congrArg (FiniteRelationModel.transition R (I (dst e)) (hst (dst e)))
      (AlgHom.congr_fun (hp e) x)
  refine ⟨t, hst, fun i ↦ Finset.subset_union_right.trans (ht i), k, hcomm, fun e ↦ ?_⟩
  apply (AlgHom.cancel_right (FiniteRelationModel.transition_surjective R (I (src e))
    (hst (src e)))).mp
  rw [AlgHom.comp_assoc, hcomm, ← AlgHom.comp_assoc, FiniteRelationModel.toQuotient_comp,
    hfac, AlgHom.comp_assoc, FiniteRelationModel.toQuotient_comp]

end FLT.Mazur.FinitePolynomialCoefficients
