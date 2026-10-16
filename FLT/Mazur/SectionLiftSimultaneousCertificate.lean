/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.SectionLiftSourceCertificate

/-!
# Common denominators for finitely many boundary sections

Separate finite source certificates combine into one certificate whose every
multiplier lifts every selected section. This supplies common neighborhoods,
not just unrelated covers for the individual generators.
-/

@[expose] public noncomputable section
namespace FLT.Mazur
variable {A B C : Type*} [CommRing A] [CommRing B] [CommRing C]
  (f : A →+* B) (g : B →+* C) {ι : Type*} (v : ι → B)

/-- The actual ideal of multipliers simultaneously lifting the selected sections. -/
def simultaneousSectionLiftIdeal (s : Finset ι) : Ideal A :=
  s.inf (fun i ↦ sectionLiftIdeal f (v i))

/-- Each common multiplier lifts every selected generator through the original map. -/
theorem mem_simultaneousSectionLiftIdeal (s : Finset ι) (a : A) :
    a ∈ simultaneousSectionLiftIdeal f v s ↔
      ∀ i ∈ s, ∃ b, f b = f a * v i := by
  simp only [simultaneousSectionLiftIdeal, Finset.inf_eq_iInf, Ideal.mem_iInf,
    mem_sectionLiftIdeal]

/-- Individual source certificates generate the unit ideal using common multipliers. -/
theorem simultaneousSectionLiftIdeal_map_eq_top (s : Finset ι)
    (hv : ∀ i ∈ s, v i ∈ sourceCertifiedSections f g) :
    (simultaneousSectionLiftIdeal f v s).map (g.comp f) = ⊤ := by
  classical
  induction s using Finset.induction_on with
  | empty => simp [simultaneousSectionLiftIdeal, Ideal.map_top]
  | @insert i s hi ih =>
    have ht : (sectionLiftIdeal f (v i)).map (g.comp f) = ⊤ := hv i (by simp)
    have hs := ih (fun j hj ↦ hv j (Finset.mem_insert_of_mem hj))
    apply top_unique
    have hm := Ideal.map_mono (f := g.comp f)
      (Ideal.mul_le_inf : sectionLiftIdeal f (v i) * simultaneousSectionLiftIdeal f v s ≤ _)
    rw [Ideal.map_mul, ht, hs, Ideal.top_mul] at hm
    simpa only [simultaneousSectionLiftIdeal, Finset.inf_insert] using hm

/-- One finite coefficient identity uses multipliers which lift all selected sections. -/
theorem simultaneous_source_lift_certificate (s : Finset ι)
    (hv : ∀ i ∈ s, v i ∈ sourceCertifiedSections f g) :
    ∃ c : simultaneousSectionLiftIdeal f v s →₀ C,
      c.sum (fun a b ↦ b * g (f a.val)) = 1 := by
  have ht := simultaneousSectionLiftIdeal_map_eq_top f g v s hv
  change Ideal.span ((g.comp f) '' (simultaneousSectionLiftIdeal f v s : Set A)) = ⊤ at ht
  have he : (g.comp f) '' (simultaneousSectionLiftIdeal f v s : Set A) =
      Set.range (fun a : simultaneousSectionLiftIdeal f v s ↦ g (f a.val)) := by
    ext a
    simp only [Set.mem_image, Set.mem_range, Subtype.exists, exists_prop,
      SetLike.mem_coe, RingHom.comp_apply]
  rwa [he, Ideal.eq_top_iff_one, Finsupp.mem_ideal_span_range_iff_exists_finsupp] at ht

end FLT.Mazur
