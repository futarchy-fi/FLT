/-
Copyright (c) 2026 krandder. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: krandder
-/
module

public import Mathlib.FieldTheory.Galois.Basic
public import Mathlib.RepresentationTheory.Homological.GroupCohomology.Hilbert90
public import Mathlib.Tactic.FieldSimp
public import Mathlib.Tactic.Ring

/-!
# Cubic Kummer parameters for finite Galois cocycles

Hilbert 90 constructs a Kummer parameter directly from a multiplicative
cocycle with values in the cube roots of unity. The parameter is a cube
in the base field precisely when the cocycle is a coboundary with a
cube-root-of-unity witness. No group cohomology quotient is constructed.
-/

@[expose] public section

namespace ThreeAdicPlan

variable {K L : Type*} [Field K] [Field L] [Algebra K L]
    [FiniteDimensional K L] [IsGalois K L]

/-- A finite Galois cocycle valued in cube roots of unity has a nonzero
Kummer parameter in the base field and an equivariant cube root upstairs. -/
theorem exists_cubic_kummer_parameter (f : Gal(L/K) → Lˣ)
    (hf : groupCohomology.IsMulCocycle₁ f) (hcube : ∀ g, f g ^ 3 = 1) :
    ∃ a : K, ∃ b : L, a ≠ 0 ∧ b ≠ 0 ∧ b ^ 3 = algebraMap K L a ∧
      ∀ g : Gal(L/K), g b = (f g : L) * b := by
  obtain ⟨b, hb⟩ := groupCohomology.isMulCoboundary₁_of_isMulCocycle₁_of_aut_to_units f hf
  have heq (g : Gal(L/K)) : g (b : L) = (f g : L) * (b : L) := by
    have h := congrArg (fun u : Lˣ ↦ (u : L)) (hb g)
    simp only [Units.val_div_eq_div_val, AlgEquiv.smul_units_def, Units.coe_map,
      MonoidHom.coe_ofClass] at h
    exact (div_eq_iff b.ne_zero).mp h
  have hfixed (g : Gal(L/K)) : g ((b : L) ^ 3) = (b : L) ^ 3 := by
    have hfg : (f g : L) ^ 3 = 1 := by
      simpa only [Units.val_pow_eq_pow_val, Units.val_one] using
        congrArg (fun u : Lˣ ↦ (u : L)) (hcube g)
    rw [map_pow, heq g, mul_pow, hfg, one_mul]
  obtain ⟨a, ha⟩ := (IsGalois.mem_range_algebraMap_iff_fixed ((b : L) ^ 3)).mpr hfixed
  refine ⟨a, b, ?_, b.ne_zero, ha.symm, heq⟩
  intro ha0
  rw [ha0, map_zero] at ha
  exact pow_ne_zero 3 b.ne_zero ha.symm

/-- A Kummer parameter is a cube in the base field exactly when its cocycle
can be represented by the coboundary of a cube root of unity. -/
theorem cubic_kummer_parameter_cube_iff (f : Gal(L/K) → Lˣ)
    (a : K) (b : L) (hb : b ≠ 0) (hpow : b ^ 3 = algebraMap K L a)
    (heq : ∀ g : Gal(L/K), g b = (f g : L) * b) :
    (∃ r : K, r ^ 3 = a) ↔
      ∃ c : L, c ^ 3 = 1 ∧ ∀ g : Gal(L/K), g c = (f g : L) * c := by
  constructor
  · rintro ⟨r, hr⟩
    have hr0 : r ≠ 0 := by
      intro hr0
      rw [hr0, zero_pow (by decide : 3 ≠ 0)] at hr
      rw [← hr, map_zero] at hpow
      exact pow_ne_zero 3 hb hpow
    refine ⟨b / algebraMap K L r, ?_, ?_⟩
    · rw [div_pow, hpow, ← map_pow, hr, div_self ((map_ne_zero (algebraMap K L)).mpr (by
        rw [← hr]; exact pow_ne_zero 3 hr0))]
    · intro g
      rw [map_div₀, heq g, AlgEquiv.commutes, mul_div_assoc]
  · rintro ⟨c, hc, hceq⟩
    have hc0 : c ≠ 0 := by
      intro hc0
      rw [hc0, zero_pow (by decide : 3 ≠ 0)] at hc
      exact zero_ne_one hc
    have hfixed (g : Gal(L/K)) : g (b / c) = b / c := by
      rw [map_div₀, heq g, hceq g, mul_div_mul_left _ _ (f g).ne_zero]
    obtain ⟨r, hr⟩ := (IsGalois.mem_range_algebraMap_iff_fixed (b / c)).mpr hfixed
    refine ⟨r, (algebraMap K L).injective ?_⟩
    rw [map_pow, hr, div_pow, hpow, hc, div_one]

end ThreeAdicPlan
