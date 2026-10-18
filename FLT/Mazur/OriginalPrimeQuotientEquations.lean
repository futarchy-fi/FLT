/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.OriginalPrimeIntegralGenerators

/-!
# Local integrality from equations modulo the bad ideal

A presentation of the ambient coordinate ring supplies generators of every
chosen quotient. Polynomial residuals in the exact bad ideal become the
equations needed for integrality at the unchanged original prime.
-/

@[expose] public noncomputable section
namespace FLT.Mazur.OriginalPrimeIntegralFiber
variable {R A I : Type*} [CommRing R] [CommRing A]
  (s : R →+* A) (J : Ideal A) (a : I → A)

/-- Ambient algebra generators descend to the full chosen quotient, with its nilpotents. -/
theorem quotient_generators
    (hgen : Subring.closure (Set.range s ∪ Set.range a) = ⊤) :
    Subring.closure (Set.range ((Ideal.Quotient.mk J).comp s) ∪
      Set.range (fun i ↦ Ideal.Quotient.mk J (a i))) = ⊤ := by
  apply top_unique
  intro x _
  obtain ⟨b, rfl⟩ := Ideal.Quotient.mk_surjective x
  have hb : b ∈ Subring.closure (Set.range s ∪ Set.range a) := hgen ▸ Subring.mem_top b
  have h := Subring.mem_closure_image_of (Ideal.Quotient.mk J) hb
  simpa only [Set.image_union, ← Set.range_comp, RingHom.coe_comp, Function.comp_def] using h

/-- Evaluation in the quotient is zero precisely when the original residual lies in the ideal. -/
theorem quotient_equation_iff (p : Polynomial R) (b : A) :
    p.eval₂ ((Ideal.Quotient.mk J).comp s) (Ideal.Quotient.mk J b) = 0 ↔
      p.eval₂ s b ∈ J := by
  rw [← Polynomial.hom_eval₂ p s (Ideal.Quotient.mk J) b,
    Ideal.Quotient.eq_zero_iff_mem]

variable [Fintype I] (P : Ideal R) [P.IsPrime]

/-- Ambient polynomial residuals construct local integrality of the exact bad quotient. -/
theorem quotient_local_integral_of_residual_equations (p : I → Polynomial R)
    (hgen : Subring.closure (Set.range s ∪ Set.range a) = ⊤)
    (heq : ∀ i, (p i).eval₂ s (a i) ∈ J)
    (hlead : (∏ i, (p i).leadingCoeff) ∉ P) :
    (localizedMap ((Ideal.Quotient.mk J).comp s) P).IsIntegral := by
  apply localizedMap_integral_of_finite_equations ((Ideal.Quotient.mk J).comp s) P
    (fun i ↦ Ideal.Quotient.mk J (a i)) p (quotient_generators s J a hgen)
  · intro i
    exact (quotient_equation_iff s J (p i) (a i)).mpr (heq i)
  · exact hlead

/-- Empty fibers and residual equations produce a scalar in the unreduced ideal itself. -/
theorem exists_scalar_mem_of_residual_equations (p : I → Polynomial R)
    (hgen : Subring.closure (Set.range s ∪ Set.range a) = ⊤)
    (heq : ∀ i, (p i).eval₂ s (a i) ∈ J)
    (hlead : (∏ i, (p i).leadingCoeff) ∉ P)
    (hP : ∀ Q : PrimeSpectrum (A ⧸ J),
      Q.asIdeal.comap ((Ideal.Quotient.mk J).comp s) ≠ P) :
    ∃ r : R, r ∉ P ∧ s r ∈ J := by
  obtain ⟨r, hr, hz⟩ := exists_kernel_scalar ((Ideal.Quotient.mk J).comp s) P
    (quotient_local_integral_of_residual_equations s J a P p hgen heq hlead) hP
  exact ⟨r, hr, Ideal.Quotient.eq_zero_iff_mem.mp hz⟩

end FLT.Mazur.OriginalPrimeIntegralFiber
