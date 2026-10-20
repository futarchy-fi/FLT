/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.HomogeneousNumeratorObstruction
public import Mathlib.Data.Fintype.Order

/-!
# One finite scalar obstruction for a whole family

Intersect exact scalar ideals over the unchanged common scalar ring. A
single scalar class encodes all errors. For a finite family, radical
membership in every constituent gives one exponent for the entire family.
This does not exchange the radical with an infinite order intersection.
-/

@[expose] public noncomputable section
namespace FLT.Mazur.FiniteScalarObstruction
variable {R : Type*} [CommRing R] {ι : Type*} (I : ι → Ideal R)

/-- Scalars solving every constituent homogeneous obstruction. -/
def jointIdeal : Ideal R := ⨅ j, I j

/-- Joint membership preserves every independent error coordinate. -/
theorem mem_jointIdeal (r : R) : r ∈ jointIdeal I ↔ ∀ j, r ∈ I j := by
  simp only [jointIdeal, Ideal.mem_iInf]

/-- The diagonal scalar obstruction is cyclic over the unchanged common scalar ring. -/
theorem jointQuotient_finite : Module.Finite R (R ⧸ jointIdeal I) := inferInstance

/-- A vanishing diagonal scalar class means every original scalar ideal contains it. -/
theorem jointQuotient_eq_zero_iff (r : R) :
    Ideal.Quotient.mk (jointIdeal I) r = 0 ↔ ∀ j, r ∈ I j := by
  rw [Ideal.Quotient.eq_zero_iff_mem, mem_jointIdeal]

variable [Finite ι]

/-- Finite individual power witnesses combine into one exponent for the entire family. -/
theorem exists_uniform_power (r : R) (h : ∀ j, r ∈ (I j).radical) :
    ∃ N : ℕ, ∀ j, r ^ N ∈ I j := by
  classical
  let _ := Fintype.ofFinite ι
  choose m hm using fun j ↦ (Ideal.mem_radical_iff).mp (h j)
  refine ⟨Finset.univ.sup m, fun j ↦ ?_⟩
  have hle : m j ≤ Finset.univ.sup m := Finset.le_sup (Finset.mem_univ j)
  have hh := (I j).mul_mem_left (r ^ (Finset.univ.sup m - m j)) (hm j)
  simpa only [← pow_add, Nat.sub_add_cancel hle] using hh

/-- Only the finite family index is interchanged with the radical. -/
theorem mem_radical_jointIdeal (r : R) :
    r ∈ (jointIdeal I).radical ↔ ∀ j, r ∈ (I j).radical := by
  constructor
  · rintro ⟨N, hN⟩ j
    exact ⟨N, (mem_jointIdeal I (r ^ N)).mp hN j⟩
  · intro h
    obtain ⟨N, hN⟩ := exists_uniform_power I r h
    exact ⟨N, (mem_jointIdeal I (r ^ N)).mpr hN⟩

end FLT.Mazur.FiniteScalarObstruction
