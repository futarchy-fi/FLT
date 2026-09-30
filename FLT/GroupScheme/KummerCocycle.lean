/-
Copyright (c) 2026 krandder. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: krandder
-/
module

public import FLT.GroupScheme.KummerParameter
public import Mathlib.FieldTheory.Galois.Basic
public import Mathlib.RepresentationTheory.Homological.GroupCohomology.Hilbert90
public import Mathlib.Tactic.FieldSimp
public import Mathlib.Tactic.Ring

/-!
# Kummer parameters of arbitrary exponent

Hilbert 90 identifies finite Galois cocycles killed by `n` with nonzero
Kummer parameters. The trivial class is detected by an `n`-th root in the
base field. A valuation criterion detects unit representatives; no
finite-flat or ramification classification is assumed.
-/

@[expose] public section

namespace KummerTheory

variable {K L : Type*} [Field K] [Field L] [Algebra K L]
    [FiniteDimensional K L] [IsGalois K L]

/-- A finite Galois cocycle valued in n-th roots of unity has a nonzero
Kummer parameter in the base field and an equivariant n-th root upstairs. -/
theorem exists_kummer_parameter {n : ℕ} (f : Gal(L/K) → Lˣ)
    (hf : groupCohomology.IsMulCocycle₁ f) (hpower : ∀ g, f g ^ n = 1) :
    ∃ a : K, ∃ b : L, a ≠ 0 ∧ b ≠ 0 ∧ b ^ n = algebraMap K L a ∧
      ∀ g : Gal(L/K), g b = (f g : L) * b := by
  obtain ⟨b, hb⟩ := groupCohomology.isMulCoboundary₁_of_isMulCocycle₁_of_aut_to_units f hf
  have heq (g : Gal(L/K)) : g (b : L) = (f g : L) * (b : L) := by
    have h := congrArg (fun u : Lˣ ↦ (u : L)) (hb g)
    simp only [Units.val_div_eq_div_val, AlgEquiv.smul_units_def, Units.coe_map,
      MonoidHom.coe_ofClass] at h
    exact (div_eq_iff b.ne_zero).mp h
  have hfixed (g : Gal(L/K)) : g ((b : L) ^ n) = (b : L) ^ n := by
    have hfg : (f g : L) ^ n = 1 := by
      simpa only [Units.val_pow_eq_pow_val, Units.val_one] using
        congrArg (fun u : Lˣ ↦ (u : L)) (hpower g)
    rw [map_pow, heq g, mul_pow, hfg, one_mul]
  obtain ⟨a, ha⟩ := (IsGalois.mem_range_algebraMap_iff_fixed ((b : L) ^ n)).mpr hfixed
  refine ⟨a, b, ?_, b.ne_zero, ha.symm, heq⟩
  intro ha0
  rw [ha0, map_zero] at ha
  exact pow_ne_zero n b.ne_zero ha.symm

/-- A Kummer parameter is an n-th power in the base field exactly when its cocycle
can be represented by the coboundary of an n-th root of unity. -/
theorem kummer_parameter_power_iff {n : ℕ} (hn : 0 < n) (f : Gal(L/K) → Lˣ)
    (a : K) (b : L) (hb : b ≠ 0) (hpow : b ^ n = algebraMap K L a)
    (heq : ∀ g : Gal(L/K), g b = (f g : L) * b) :
    (∃ r : K, r ^ n = a) ↔
      ∃ c : L, c ^ n = 1 ∧ ∀ g : Gal(L/K), g c = (f g : L) * c := by
  constructor
  · rintro ⟨r, hr⟩
    have hr0 : r ≠ 0 := by
      intro hr0
      rw [hr0, zero_pow hn.ne'] at hr
      rw [← hr, map_zero] at hpow
      exact pow_ne_zero n hb hpow
    refine ⟨b / algebraMap K L r, ?_, ?_⟩
    · rw [div_pow, hpow, ← map_pow, hr, div_self ((map_ne_zero (algebraMap K L)).mpr (by
        rw [← hr]; exact pow_ne_zero n hr0))]
    · intro g
      rw [map_div₀, heq g, AlgEquiv.commutes, mul_div_assoc]
  · rintro ⟨c, hc, hceq⟩
    have hc0 : c ≠ 0 := by
      intro hc0
      rw [hc0, zero_pow hn.ne'] at hc
      exact zero_ne_one hc
    have hfixed (g : Gal(L/K)) : g (b / c) = b / c := by
      rw [map_div₀, heq g, hceq g, mul_div_mul_left _ _ (f g).ne_zero]
    obtain ⟨r, hr⟩ := (IsGalois.mem_range_algebraMap_iff_fixed (b / c)).mpr hfixed
    refine ⟨r, (algebraMap K L).injective ?_⟩
    rw [map_pow, hr, div_pow, hpow, hc, div_one]

end KummerTheory

namespace ValuationSubring

variable {K : Type*} [Field K] (A : ValuationSubring K)

/-- A Kummer class has a unit representative exactly when its valuation
can be removed by an `n`-th power in the base field. -/
theorem exists_unit_factor_iff (n : ℕ) (q : Kˣ) :
    (∃ b : Kˣ, A.valuation (q : K) = A.valuation (b : K) ^ n) ↔
      ∃ b : Kˣ, ∃ u : Aˣ, q = b ^ n * Units.map A.subtype.toMonoidHom u := by
  constructor
  · rintro ⟨b, hb⟩
    obtain ⟨u, hu⟩ := A.exists_unit_factor_of_valuation_eq_pow n q b hb
    exact ⟨b, u, hu⟩
  · rintro ⟨b, u, rfl⟩
    refine ⟨b, ?_⟩
    simp only [Units.val_mul, Units.val_pow_eq_pow_val, Units.coe_map,
      map_mul, map_pow]
    change A.valuation (b : K) ^ n * A.valuation ((u : A) : K) = _
    rw [(A.valuation_eq_one_iff (u : A)).mp u.isUnit, mul_one]

end ValuationSubring
