/-
Copyright (c) 2026 krandder. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: krandder
-/
module

public import FLT.GroupScheme.PointDifferentials
public import Mathlib.RingTheory.Conductor

/-!
# Conductor ideals and differential annihilators

The conductor of an arbitrary subalgebra is the largest ideal of the ambient
algebra contained in it. If an integer annihilates the differentials of the
subalgebra, its product with the conductor annihilates the differentials of
the ambient algebra. No bound on the conductor is asserted.
-/

@[expose] public noncomputable section

namespace Subalgebra

variable {R B : Type*} [CommRing R] [CommRing B] [Algebra R B]

/-- The largest ideal of the ambient algebra contained in a subalgebra. -/
def conductorIdeal (S : Subalgebra R B) : Ideal B where
  carrier := {c | ∀ b : B, c * b ∈ S}
  zero_mem' b := by simp only [zero_mul, zero_mem]
  add_mem' hc hd b := by simpa only [add_mul] using S.add_mem (hc b) (hd b)
  smul_mem' b c hc d := by
    simpa only [smul_eq_mul, mul_left_comm, mul_assoc] using hc (b * d)

/-- Membership in the conductor means that every multiple belongs to the subalgebra. -/
@[simp] theorem mem_conductorIdeal (S : Subalgebra R B) (c : B) :
    c ∈ S.conductorIdeal ↔ ∀ b : B, c * b ∈ S := Iff.rfl

/-- Every conductor element belongs to the subalgebra. -/
theorem conductorIdeal_subset (S : Subalgebra R B) : (S.conductorIdeal : Set B) ⊆ S :=
  fun c hc ↦ by
    change c ∈ S
    simpa only [mul_one] using hc 1

/-- An ideal lies in the conductor exactly when it lies in the subalgebra. -/
theorem le_conductorIdeal_iff (S : Subalgebra R B) (I : Ideal B) :
    I ≤ S.conductorIdeal ↔ (I : Set B) ⊆ S := by
  constructor
  · exact fun h _ hc ↦ S.conductorIdeal_subset (h hc)
  · exact fun h c hc b ↦ h (I.mul_mem_right b hc)

/-- This conductor agrees with mathlib's conductor for a singly generated subalgebra. -/
theorem conductorIdeal_adjoin_singleton (x : B) :
    (Algebra.adjoin R {x}).conductorIdeal = conductor R x := rfl

/-- A subalgebra has unit conductor exactly when it is the whole algebra. -/
@[simp] theorem conductorIdeal_eq_top_iff (S : Subalgebra R B) :
    S.conductorIdeal = ⊤ ↔ S = ⊤ := by
  rw [Ideal.eq_top_iff_one, mem_conductorIdeal]
  simp only [one_mul]
  exact ⟨fun h ↦ top_unique (fun x _ ↦ h x), fun h x ↦ by simp [h]⟩

/-- Multiplying a differential annihilator by a conductor element gives an
annihilator of the ambient algebra's differentials. -/
theorem nat_mul_mem_annihilator_kaehlerDifferential (S : Subalgebra R B) (n : ℕ)
    (hn : ∀ ω : KaehlerDifferential R S, n • ω = 0)
    {c : B} (hc : c ∈ S.conductorIdeal) :
    (n : B) * c ∈ Module.annihilator B (KaehlerDifferential R B) := by
  rw [Module.mem_annihilator]
  intro ω
  have h := KaehlerDifferential.nsmul_smul_eq_zero_of_conductor n hn c
    (fun b ↦ ⟨⟨c * b, hc b⟩, rfl⟩) ω
  simpa only [mul_smul, Nat.cast_smul_eq_nsmul] using h

/-- The product of an integer annihilator and the conductor is contained in
the annihilator of the ambient Kähler differentials. -/
theorem span_nat_mul_conductorIdeal_le_annihilator (S : Subalgebra R B) (n : ℕ)
    (hn : ∀ ω : KaehlerDifferential R S, n • ω = 0) :
    Ideal.span {(n : B)} * S.conductorIdeal ≤
      Module.annihilator B (KaehlerDifferential R B) := by
  exact Ideal.span_singleton_mul_le_iff.mpr fun _ hc ↦
    S.nat_mul_mem_annihilator_kaehlerDifferential n hn hc

end Subalgebra

namespace ThreeAdicPlan

variable {R K B : Type} [CommRing R] [Field K] [PerfectField K]
  [Algebra R K] [IsFractionRing R K] [CommRing B] [Algebra R B]

/-- The actual point-image conductor, multiplied by the exponent of a finite
flat model, annihilates the differentials of the target algebra. -/
theorem FF.span_nat_mul_point_conductor_le_annihilator (M : FF R K)
    (n : ℕ) (hn : KilledBy n M) (f : M.CoordinateRing →ₐ[R] B) :
    Ideal.span {(n : B)} * f.range.conductorIdeal ≤
      Module.annihilator B (KaehlerDifferential R B) :=
  f.range.span_nat_mul_conductorIdeal_le_annihilator n
    (M.nsmul_differential_point_range_eq_zero n hn f)

end ThreeAdicPlan
