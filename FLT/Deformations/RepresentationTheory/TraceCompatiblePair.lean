/-
Copyright (c) 2026 FLT contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: FLT contributors
-/
module

public import Mathlib.RingTheory.SimpleRing.Basic

/-!
# Trace compatibility between two coefficient fields

A common coefficient at each good index suffices to transport the trace formula
`1 + n` between two specializations. No representations at other primes are needed.
-/

@[expose] public section

namespace GaloisRepresentation

variable {ι E A B : Type*} [Field E] [CommRing A] [Nontrivial A] [CommRing B]

/-- Two trace functions are images of common coefficients at all good indices. -/
def TraceCompatiblePair (φ : E →+* A) (ψ : E →+* B)
    (good : ι → Prop) (left : ι → A) (right : ι → B) : Prop :=
  ∃ a : ι → E, ∀ i, good i → left i = φ (a i) ∧ right i = ψ (a i)

/-- An integral trace formula at one specialization determines it at the other. -/
theorem TraceCompatiblePair.transport_one_add
    {φ : E →+* A} {ψ : E →+* B} {good : ι → Prop}
    {left : ι → A} {right : ι → B}
    (h : TraceCompatiblePair φ ψ good left right) (n : ι → ℕ)
    (hleft : ∀ i, good i → left i = 1 + n i) :
    ∀ i, good i → right i = 1 + n i := by
  obtain ⟨a, ha⟩ := h
  intro i hi
  obtain ⟨hl, hr⟩ := ha i hi
  have hc : a i = 1 + (n i : E) := by
    apply φ.injective
    simpa only [map_add, map_one, map_natCast] using hl.symm.trans (hleft i hi)
  rw [hr, hc, map_add, map_one, map_natCast]

end GaloisRepresentation
