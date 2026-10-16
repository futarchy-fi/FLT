/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.SectionLiftIdealAlgebra
public import Mathlib.RingTheory.Ideal.Maps
public import Mathlib.RingTheory.Ideal.Finsupp

/-!
# The ring of sections with finite lifting certificates on a source

The coefficients of a certificate live in a further source ring, and need
not descend. Ideal multiplication nevertheless combines certificates for
sums and products. The resulting subring is defined by actual multiplier
ideals, rather than a supplied local lifting property.
-/

@[expose] public noncomputable section
namespace FLT.Mazur
variable {A B C : Type*} [CommRing A] [CommRing B] [CommRing C]
  (f : A →+* B) (g : B →+* C)

/-- The ideal generated on the tested source by all actual lifting multipliers. -/
def sectionLiftSourceIdeal (t : B) : Ideal C :=
  (sectionLiftIdeal f t).map (g.comp f)

/-- A known lift supplies a source unit-ideal certificate. -/
theorem sectionLiftSourceIdeal_image (a : A) :
    sectionLiftSourceIdeal f g (f a) = ⊤ := by
  rw [sectionLiftSourceIdeal, sectionLiftIdeal_image, Ideal.map_top]

/-- Source certificates survive negation without changing their ideal. -/
theorem sectionLiftSourceIdeal_neg (t : B) :
    sectionLiftSourceIdeal f g (-t) = sectionLiftSourceIdeal f g t := by
  rw [sectionLiftSourceIdeal, sectionLiftIdeal_neg]
  rfl

/-- The product source certificate is contained in the sum's multiplier ideal. -/
theorem sectionLiftSourceIdeal_mul_le_add (t u : B) :
    sectionLiftSourceIdeal f g t * sectionLiftSourceIdeal f g u ≤
      sectionLiftSourceIdeal f g (t + u) := by
  rw [sectionLiftSourceIdeal, sectionLiftSourceIdeal, ← Ideal.map_mul]
  exact Ideal.map_mono (sectionLiftIdeal_mul_le_add f t u)

/-- The product source certificate also certifies the product of the sections. -/
theorem sectionLiftSourceIdeal_mul_le_mul (t u : B) :
    sectionLiftSourceIdeal f g t * sectionLiftSourceIdeal f g u ≤
      sectionLiftSourceIdeal f g (t * u) := by
  rw [sectionLiftSourceIdeal, sectionLiftSourceIdeal, ← Ideal.map_mul]
  exact Ideal.map_mono (sectionLiftIdeal_mul_le_mul f t u)

/-- The actual sections with source coverage form a subring of the boundary sections. -/
def sourceCertifiedSections : Subring B where
  carrier := {t | sectionLiftSourceIdeal f g t = ⊤}
  zero_mem' := by
    change sectionLiftSourceIdeal f g 0 = ⊤
    simpa only [map_zero] using sectionLiftSourceIdeal_image f g 0
  one_mem' := by
    change sectionLiftSourceIdeal f g 1 = ⊤
    simpa only [map_one] using sectionLiftSourceIdeal_image f g 1
  add_mem' := by
    intro t u ht hu
    change sectionLiftSourceIdeal f g t = ⊤ at ht
    change sectionLiftSourceIdeal f g u = ⊤ at hu
    apply top_unique
    simpa only [ht, hu, Ideal.top_mul] using sectionLiftSourceIdeal_mul_le_add f g t u
  mul_mem' := by
    intro t u ht hu
    change sectionLiftSourceIdeal f g t = ⊤ at ht
    change sectionLiftSourceIdeal f g u = ⊤ at hu
    apply top_unique
    simpa only [ht, hu, Ideal.top_mul] using sectionLiftSourceIdeal_mul_le_mul f g t u
  neg_mem' := by
    intro t ht
    exact (sectionLiftSourceIdeal_neg f g t).trans ht

/-- Membership gives a finite coefficient identity using actual lifting multipliers. -/
theorem mem_sourceCertifiedSections_iff (t : B) :
    t ∈ sourceCertifiedSections f g ↔
      ∃ c : sectionLiftIdeal f t →₀ C,
        c.sum (fun a b ↦ b * g (f a.val)) = 1 := by
  change Ideal.span ((g.comp f) '' (sectionLiftIdeal f t : Set A)) = ⊤ ↔ _
  have h : (g.comp f) '' (sectionLiftIdeal f t : Set A) =
      Set.range (fun a : sectionLiftIdeal f t ↦ g (f a.val)) := by
    ext a
    simp only [Set.mem_image, Set.mem_range, Subtype.exists, exists_prop,
      SetLike.mem_coe, RingHom.comp_apply]
  rw [h, Ideal.eq_top_iff_one, Finsupp.mem_ideal_span_range_iff_exists_finsupp]

/-- Every original scalar belongs to the constructed subring. -/
theorem image_mem_sourceCertifiedSections (a : A) :
    f a ∈ sourceCertifiedSections f g := sectionLiftSourceIdeal_image f g a

/-- Certifying generators constructs certificates for every element of their ring closure. -/
theorem closure_le_sourceCertifiedSections (s : Set B)
    (hs : ∀ t ∈ s, t ∈ sourceCertifiedSections f g) :
    Subring.closure (Set.range f ∪ s) ≤ sourceCertifiedSections f g := by
  apply Subring.closure_le.mpr
  rintro t (⟨a, rfl⟩ | ht)
  · exact image_mem_sourceCertifiedSections f g a
  · exact hs t ht

end FLT.Mazur
