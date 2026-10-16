/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.SectionLiftSourceCertificate
public import Mathlib.Algebra.MvPolynomial.Eval

/-!
# Polynomial and inverse certificates for local boundary lifting

Polynomial expressions inherit actual finite source certificates from their
generators. For a unit section, a lifted numerator becomes a denominator for
the inverse; multiplication by the inverse on the tested source transports
the original coefficient identity.
-/

@[expose] public noncomputable section
namespace FLT.Mazur
variable {A B C : Type*} [CommRing A] [CommRing B] [CommRing C]
  (f : A →+* B) (g : B →+* C)

/-- Reversing numerator and denominator transfers the certificate to an inverse. -/
theorem sectionLiftSourceIdeal_le_inverse {t u : B} (htu : t * u = 1) :
    sectionLiftSourceIdeal f g t ≤ sectionLiftSourceIdeal f g u := by
  apply Ideal.map_le_iff_le_comap.mpr
  intro s hs
  obtain ⟨a, ha⟩ := hs
  have hm : g (f a) ∈ sectionLiftSourceIdeal f g u :=
    Ideal.mem_map_of_mem (g.comp f) (sectionLiftIdeal_inverse_multiplier f htu ha)
  have he : f a * u = f s := by rw [ha, mul_assoc, htu, mul_one]
  have h := (sectionLiftSourceIdeal f g u).mul_mem_left (g u) hm
  rw [mul_comm, ← map_mul, he] at h
  exact h

/-- A certified unit has a certified inverse, without any invariant-coefficient hypothesis. -/
theorem inverse_mem_sourceCertifiedSections {t u : B} (htu : t * u = 1)
    (ht : t ∈ sourceCertifiedSections f g) : u ∈ sourceCertifiedSections f g := by
  apply top_unique
  exact ht ▸ sectionLiftSourceIdeal_le_inverse f g htu

/-- Every polynomial in certified generators has a finite source lifting certificate. -/
theorem polynomial_mem_sourceCertifiedSections {ι : Type*} (v : ι → B)
    (hv : ∀ i, v i ∈ sourceCertifiedSections f g) (P : MvPolynomial ι A) :
    MvPolynomial.eval₂ f v P ∈ sourceCertifiedSections f g :=
  MvPolynomial.eval₂_mem (fun _ _ ↦ image_mem_sourceCertifiedSections f g _) hv

/-- The resulting polynomial certificate uses the original ring's actual lifting multipliers. -/
theorem polynomial_source_lift_certificate {ι : Type*} (v : ι → B)
    (hv : ∀ i, v i ∈ sourceCertifiedSections f g) (P : MvPolynomial ι A) :
    ∃ c : sectionLiftIdeal f (MvPolynomial.eval₂ f v P) →₀ C,
      c.sum (fun a b ↦ b * g (f a.val)) = 1 :=
  (mem_sourceCertifiedSections_iff f g _).mp
    (polynomial_mem_sourceCertifiedSections f g v hv P)

/-- Certified polynomial numerators and unit denominators give certified rational expressions. -/
theorem polynomial_fraction_mem_sourceCertifiedSections {ι : Type*} (v : ι → B)
    (hv : ∀ i, v i ∈ sourceCertifiedSections f g) (P Q : MvPolynomial ι A)
    (u : B) (hu : MvPolynomial.eval₂ f v Q * u = 1) :
    MvPolynomial.eval₂ f v P * u ∈ sourceCertifiedSections f g :=
  (sourceCertifiedSections f g).mul_mem
    (polynomial_mem_sourceCertifiedSections f g v hv P)
    (inverse_mem_sourceCertifiedSections f g hu
      (polynomial_mem_sourceCertifiedSections f g v hv Q))

end FLT.Mazur
