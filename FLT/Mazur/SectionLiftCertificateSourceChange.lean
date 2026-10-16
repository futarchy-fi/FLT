/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.SectionLiftSourceCertificate
public import Mathlib.RingTheory.Flat.FaithfullyFlat.Algebra

/-!
# Descent of lifting certificates from a faithfully flat source test

Changing only the tested source ring preserves the actual multiplier ideal.
Faithfully flat tests reflect its unit-ideal condition, and therefore return
a finite certificate with coefficients in the original source ring.
-/

@[expose] public noncomputable section
namespace FLT.Mazur
variable {A B C D : Type*} [CommRing A] [CommRing B] [CommRing C] [CommRing D]
  (f : A →+* B) (g : B →+* C) (h : C →+* D)

/-- The tested ideal changes by ordinary extension of the original source ideal. -/
theorem sectionLiftSourceIdeal_comp (t : B) :
    sectionLiftSourceIdeal f (h.comp g) t = (sectionLiftSourceIdeal f g t).map h := by
  simp only [sectionLiftSourceIdeal, Ideal.map_map, RingHom.comp_assoc]

/-- Every source certificate remains a certificate after any ring map of tested sources. -/
theorem sourceCertifiedSections_le_comp :
    sourceCertifiedSections f g ≤ sourceCertifiedSections f (h.comp g) := by
  intro t ht
  change sectionLiftSourceIdeal f (h.comp g) t = ⊤
  rw [sectionLiftSourceIdeal_comp, show sectionLiftSourceIdeal f g t = ⊤ from ht,
    Ideal.map_top]

variable [Algebra C D] [Module.FaithfullyFlat C D]

/-- Faithful flatness reflects precisely the original source certificate condition. -/
theorem sectionLiftSourceIdeal_faithfullyFlat_iff (t : B) :
    sectionLiftSourceIdeal f ((algebraMap C D).comp g) t = ⊤ ↔
      sectionLiftSourceIdeal f g t = ⊤ := by
  rw [sectionLiftSourceIdeal_comp]
  constructor
  · intro ht
    apply Ideal.map_injective_of_faithfullyFlat (B := D)
    exact ht.trans (Ideal.map_top _).symm
  · intro ht
    rw [ht, Ideal.map_top]

/-- The certified subring is unchanged by a faithfully flat test of the source. -/
theorem sourceCertifiedSections_faithfullyFlat :
    sourceCertifiedSections f ((algebraMap C D).comp g) = sourceCertifiedSections f g := by
  ext t
  exact sectionLiftSourceIdeal_faithfullyFlat_iff f g t

/-- A finite coefficient identity after a faithful flat test descends to original coefficients. -/
theorem source_lift_certificate_descends (t : B)
    (hd : ∃ a : sectionLiftIdeal f t →₀ D,
      a.sum (fun v b ↦ b * algebraMap C D (g (f v.val))) = 1) :
    ∃ a : sectionLiftIdeal f t →₀ C,
      a.sum (fun v b ↦ b * g (f v.val)) = 1 := by
  apply (mem_sourceCertifiedSections_iff f g t).mp
  rw [← sourceCertifiedSections_faithfullyFlat f g (D := D)]
  exact (mem_sourceCertifiedSections_iff f ((algebraMap C D).comp g) t).mpr hd

end FLT.Mazur
