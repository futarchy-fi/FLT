/-
Copyright (c) 2026 krandder. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: krandder
-/
module

public import Mathlib.RingTheory.Henselian

/-!
# Henselian root lifting along a ring equivalence

Transport the root-lifting construction itself, including its congruence to
the given approximate root. This applies to the canonical image of a DVR
inside its fraction field.
-/

@[expose] public section

namespace FLT.Mazur

open IsLocalRing Polynomial

variable {R S : Type*} [CommRing R] [CommRing S]
  [HenselianLocalRing R] [IsLocalRing S]

/-- Henselian root lifting is preserved by an actual ring equivalence. -/
theorem henselianLocalRing_of_ringEquiv (e : R ≃+* S) : HenselianLocalRing S := by
  constructor
  intro f hf b hb hu
  have heval (g : S[X]) (x : S) :
      (g.map e.symm.toRingHom).eval (e.symm x) = e.symm (g.eval x) :=
    eval_map_apply e.symm.toRingHom x
  have hm (x : S) : e.symm x ∈ maximalIdeal R ↔ x ∈ maximalIdeal S := by
    rw [mem_maximalIdeal, mem_maximalIdeal]
    exact not_congr (isUnit_map_iff e.symm x)
  obtain ⟨a, ha, hab⟩ := HenselianLocalRing.is_henselian
    (f.map e.symm.toRingHom) (hf.map _) (e.symm b)
    (by rw [heval]; exact (hm _).mpr hb)
    (by rw [derivative_map, heval]; exact hu.map e.symm.toRingHom)
  refine ⟨e a, ?_, ?_⟩
  · apply e.symm.injective
    simpa only [IsRoot, ← heval, RingEquiv.symm_apply_apply, map_zero] using ha
  · apply (hm _).mp
    simpa only [map_sub, RingEquiv.symm_apply_apply] using hab

end FLT.Mazur
