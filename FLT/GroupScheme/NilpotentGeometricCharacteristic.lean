/-
Copyright (c) 2026 krandder. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: krandder
-/
module

public import Mathlib.Algebra.CharP.Basic
public import Mathlib.RingTheory.Ideal.Quotient.Operations
public import Mathlib.RingTheory.Nilpotent.Basic

/-! # Geometric points of a nilpotent thickening

Every field-valued point kills nilpotents. In particular, the geometric
points of a p-nilpotent test algebra have characteristic p.
-/

@[expose] public noncomputable section
namespace RingHom
variable {B C S : Type*} [CommRing B] [CommRing C] [CommRing S] [IsReduced S]

/-- Maps to reduced rings kill a nilpotent coefficient kernel. -/
theorem ker_le_of_nilpotent_kernel (q : B →+* C) (x : B →+* S)
    {n : ℕ} (hn : RingHom.ker q ^ n = ⊥) : RingHom.ker q ≤ RingHom.ker x := by
  intro b hb
  have hpow : b ^ n = 0 := by
    have hmem := Ideal.pow_mem_pow hb n
    rwa [hn, Ideal.mem_bot] at hmem
  exact (show IsNilpotent (x b) from ⟨n, by rw [← map_pow, hpow, map_zero]⟩).eq_zero

/-- Every reduced-valued point factors uniquely through a nilpotent surjection. -/
theorem existsUnique_lift_of_nilpotent_kernel (q : B →+* C)
    (hq : Function.Surjective q) {n : ℕ} (hn : RingHom.ker q ^ n = ⊥)
    (x : B →+* S) : ∃! y : C →+* S, y.comp q = x := by
  let y := q.liftOfSurjective hq ⟨x, ker_le_of_nilpotent_kernel q x hn⟩
  have hy : y.comp q = x := RingHom.liftOfSurjective_comp q hq _
  refine ⟨y, hy, ?_⟩
  intro z hz
  ext c
  obtain ⟨b, rfl⟩ := hq c
  exact (RingHom.congr_fun hz b).trans
    (RingHom.congr_fun hy b).symm

/-- A geometric point of a p-nilpotent algebra has characteristic p. -/
theorem charP_of_nilpotent_natCast {Ω : Type*} [Field Ω] (x : B →+* Ω)
    (p : ℕ) (hp : p.Prime) (h : IsNilpotent (p : B)) : CharP Ω p := by
  apply (CharP.charP_iff_prime_eq_zero hp).2
  have hz := (h.map x).eq_zero
  simpa only [map_natCast] using hz

end RingHom
