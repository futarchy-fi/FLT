/-
Copyright (c) 2026 krandder. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: krandder
-/
module

public import Mathlib.RingTheory.Ideal.Quotient.Operations

/-! # Lift a unit-ideal certificate through a finitely generated relation ideal -/

@[expose] public noncomputable section

namespace Ideal

variable {R ι κ : Type*} [CommRing R] [Fintype ι] [Fintype κ]

/-- A finite family spanning the unit ideal in a relation quotient has a polynomial-style
certificate: a combination of the opens plus a combination of the relations equals one. -/
theorem exists_unit_certificate_of_quotient_span_eq_top (f : ι → R) (g : κ → R)
    (h : span (Set.range fun j ↦ Quotient.mk (span (Set.range f)) (g j)) = ⊤) :
    ∃ (a : κ → R) (b : ι → R), ∑ j, a j * g j + ∑ i, b i * f i = 1 := by
  let I := span (Set.range f)
  obtain ⟨c, hc⟩ := mem_span_range_iff_exists_fun.mp ((eq_top_iff_one _).mp h)
  choose a ha using fun j ↦ Quotient.mk_surjective (c j)
  have hm : (1 - ∑ j, a j * g j) ∈ I := by
    apply Quotient.eq_zero_iff_mem.mp
    simpa [I, map_sub, map_sum, map_mul, ha] using sub_eq_zero.mpr hc.symm
  obtain ⟨b, hb⟩ := mem_span_range_iff_exists_fun.mp hm
  exact ⟨a, b, by rw [hb]; ring⟩

end Ideal
