/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.SectionLiftSourceCertificate

/-!
# Transport of actual lifting certificates through ring coordinates

Commuting ring equivalences transport the entire multiplier ideal and source
certificate. This compares tensor coordinates with full invariant equalizers,
without replacing the tested source by an abstract quotient.
-/

@[expose] public noncomputable section
namespace FLT.Mazur.SectionLiftCertificateEquiv
variable {A B C A' B' C' : Type*}
  [CommRing A] [CommRing B] [CommRing C]
  [CommRing A'] [CommRing B'] [CommRing C']
  (f : A →+* B) (g : B →+* C) (f' : A' →+* B') (g' : B' →+* C')
  (a : A ≃+* A') (b : B ≃+* B') (c : C ≃+* C')
  (hf : ∀ x, f' (a x) = b (f x)) (hg : ∀ x, g' (b x) = c (g x))

include hf in
/-- The full multiplier equation is independent of the chosen ring coordinates. -/
theorem multiplier_mem_iff (t : B) (x : A) :
    a x ∈ sectionLiftIdeal f' (b t) ↔ x ∈ sectionLiftIdeal f t := by
  constructor
  · rintro ⟨y, hy⟩
    refine ⟨a.symm y, b.injective ?_⟩
    rw [← hf, a.apply_symm_apply, hy, map_mul, hf]
  · rintro ⟨y, hy⟩
    refine ⟨a y, ?_⟩
    rw [hf, hy, map_mul, hf]

include hf in
/-- A change of ring coordinates transports the complete lifting ideal. -/
theorem ideal_map (t : B) :
    (sectionLiftIdeal f t).map a.toRingHom = sectionLiftIdeal f' (b t) := by
  apply le_antisymm
  · apply Ideal.map_le_iff_le_comap.mpr
    intro x hx
    exact (multiplier_mem_iff f f' a b hf t x).mpr hx
  · intro y hy
    obtain ⟨x, rfl⟩ := a.surjective y
    exact Ideal.mem_map_of_mem a.toRingHom
      ((multiplier_mem_iff f f' a b hf t x).mp hy)

include hf hg in
/-- The actual tested ideal is transported through the source coordinate equivalence. -/
theorem sourceIdeal_map (t : B) :
    (sectionLiftSourceIdeal f g t).map c.toRingHom =
      sectionLiftSourceIdeal f' g' (b t) := by
  unfold sectionLiftSourceIdeal
  rw [← ideal_map f f' a b hf, Ideal.map_map, Ideal.map_map]
  congr 1
  ext x
  exact ((hg (f x)).symm.trans (congrArg g' (hf x).symm))

include hf hg in
/-- Full invariant coordinates and tensor coordinates certify precisely the same section. -/
theorem certified_iff (t : B) :
    b t ∈ sourceCertifiedSections f' g' ↔ t ∈ sourceCertifiedSections f g := by
  change sectionLiftSourceIdeal f' g' (b t) = ⊤ ↔ sectionLiftSourceIdeal f g t = ⊤
  rw [← sourceIdeal_map f g f' g' a b c hf hg]
  constructor
  · intro h
    have he := congrArg (Ideal.map c.symm.toRingHom) h
    have hc : c.symm.toRingHom.comp c.toRingHom = RingHom.id C := by
      ext x
      exact c.symm_apply_apply x
    simpa only [Ideal.map_map, hc, Ideal.map_id, Ideal.map_top] using he
  · intro h
    rw [h, Ideal.map_top]

end FLT.Mazur.SectionLiftCertificateEquiv
