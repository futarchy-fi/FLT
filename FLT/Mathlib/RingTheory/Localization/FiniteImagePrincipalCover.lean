/-
Copyright (c) 2026 krandder. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: krandder
-/
module

public import Mathlib.RingTheory.Ideal.Maximal
public import Mathlib.RingTheory.Ideal.Span

/-! # Finite principal neighbourhoods covering the image of a map of spectra -/

@[expose] public noncomputable section

namespace RingHom

variable {R S : Type*} [CommRing R] [CommRing S]

/-- Principal neighbourhoods at the images of all primes have a finite subfamily whose
images generate the unit ideal. The actual elements of the source ring are retained. -/
theorem exists_finite_image_principal_cover (f : R →+* S) (P : R → Prop)
    (h : ∀ (q : Ideal S) [q.IsPrime], ∃ a : R, f a ∉ q ∧ P a) :
    ∃ (t : Finset S) (a : t → R), (∀ i, P (a i)) ∧
      (∀ i, f (a i) = i.val) ∧ Ideal.span (Set.range fun i ↦ f (a i)) = ⊤ := by
  classical
  let U := f '' {a | P a}
  have hU : Ideal.span U = ⊤ := by
    by_contra hn
    obtain ⟨q, hq, hle⟩ := Ideal.exists_le_maximal (Ideal.span U) hn
    have : q.IsMaximal := hq
    obtain ⟨a, ha, hPa⟩ := h q
    exact ha (hle (Ideal.subset_span ⟨a, hPa, rfl⟩))
  obtain ⟨t, ht, hspan⟩ := (Ideal.span_eq_top_iff_finite U).mp hU
  have hex (i : t) : ∃ a : R, P a ∧ f a = i.val := ht i.property
  choose a ha he using hex
  refine ⟨t, a, ha, he, ?_⟩
  have hr : Set.range (fun i ↦ f (a i)) = (t : Set S) := by
    ext x
    constructor
    · rintro ⟨i, rfl⟩
      change f (a i) ∈ (t : Set S)
      rw [he]
      exact i.property
    · intro hx
      exact ⟨⟨x, hx⟩, he ⟨x, hx⟩⟩
  rwa [hr]

end RingHom
