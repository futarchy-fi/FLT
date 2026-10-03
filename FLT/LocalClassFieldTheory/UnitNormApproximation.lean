/-
Copyright (c) 2026 krandder. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: krandder
-/
module

public import FLT.LocalClassFieldTheory.PrincipalNormCorrection
public import FLT.LocalClassFieldTheory.ResidueNormLift

/-!
# Improving unit norm approximations

Starting from the residue norm, a principal-unit correction improves the
precision by one while changing the chosen unit only at the previous precision.
-/

@[expose] public noncomputable section

namespace LocalClassFieldTheory

open IsLocalRing

/-- Multiplicative and additive congruences of units are equivalent. -/
theorem unit_div_mem_principalUnits {A : Type*} [CommRing A]
    (π : A) (n : ℕ) (a b : Aˣ) :
    a / b ∈ principalUnits π n ↔ π ^ n ∣ (a : A) - (b : A) := by
  rw [mem_principalUnits]
  constructor
  · intro h
    convert dvd_mul_of_dvd_left h (b : A) using 1
    simp [div_eq_mul_inv, sub_mul, mul_assoc]
  · intro h
    convert dvd_mul_of_dvd_left h ((b⁻¹ : Aˣ) : A) using 1
    simp [div_eq_mul_inv, sub_mul]

variable (R S : Type*) [CommRing R] [IsDomain R] [IsDiscreteValuationRing R]
  [CommRing S] [IsDomain S] [IsDiscreteValuationRing S]
  [Algebra R S] [IsLocalHom (algebraMap R S)]
  [Module.Free R S] [Module.Finite R S] [Algebra.FormallyUnramified R S]
  {π : R} (hπ : Irreducible π)

include hπ in
/-- Improve a norm approximation by a correction at the same principal-unit level. -/
theorem exists_unit_norm_improvement (u : Rˣ) (n : ℕ) (hn : 0 < n) (v : Sˣ)
    (hv : Units.map (Algebra.norm R) v / u ∈ principalUnits π n) :
    ∃ w : Sˣ, Units.map (Algebra.norm R) w / u ∈ principalUnits π (n + 1) ∧
      (algebraMap R S π) ^ n ∣ (w : S) - (v : S) := by
  let e : principalUnits π n := ⟨u / Units.map (Algebra.norm R) v, by
    simpa only [inv_div] using (principalUnits π n).inv_mem hv⟩
  obtain ⟨c, hc⟩ := exists_principalNorm_correction R S hπ n hn e
  refine ⟨v * c.val, ?_, ?_⟩
  · convert hc using 1
    change Units.map (Algebra.norm R) (v * c.val) / u =
      Units.map (Algebra.norm R) c.val / (u / Units.map (Algebra.norm R) v)
    simp [map_mul, div_eq_mul_inv, mul_comm, mul_left_comm]
  · have hd := (mem_principalUnits _ _ c.val).1 c.property
    convert dvd_mul_of_dvd_right hd (v : S) using 1
    simp [mul_sub]

include hπ in
/-- The residue-field norm supplies the first approximation. -/
theorem exists_unit_norm_initial [Finite (ResidueField R)] (u : Rˣ) :
    ∃ v : Sˣ, Units.map (Algebra.norm R) v / u ∈ principalUnits π 1 := by
  obtain ⟨v, hv⟩ := exists_unit_norm_sub_mem R S u
  refine ⟨v, (unit_div_mem_principalUnits π 1 _ _).2 ?_⟩
  change π ^ 1 ∣ Algebra.norm R (v : S) - (u : R)
  simpa only [pow_one, hπ.maximalIdeal_eq, Ideal.mem_span_singleton] using hv

end LocalClassFieldTheory
