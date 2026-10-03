/-
Copyright (c) 2026 krandder. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: krandder
-/
module

public import FLT.GroupScheme.KummerCocycle
public import Mathlib.GroupTheory.QuotientGroup.Basic

/-!
# Independent Kummer power classes and their unit subgroup

Power classes are defined directly from the multiplicative group of the
field. The unit subgroup is the image of valuation-ring units. Neither
definition refers to representations, finite-flat models or ramification.
-/

@[expose] public section

namespace KummerTheory

variable (K : Type*) [Field K]

/-- Multiplicative classes modulo nth powers. -/
abbrev PowerClass (n : ℕ) := Kˣ ⧸ (powMonoidHom n : Kˣ →* Kˣ).range

variable {K}

/-- The quotient map to multiplicative power classes. -/
def powerClassMap (n : ℕ) : Kˣ →* PowerClass K n :=
  QuotientGroup.mk' (powMonoidHom n : Kˣ →* Kˣ).range

/-- The subgroup of power classes represented by units of the valuation ring. -/
def unitClasses (A : ValuationSubring K) (n : ℕ) : Subgroup (PowerClass K n) :=
  ((powerClassMap n).comp (Units.map A.subtype.toMonoidHom)).range

/-- A power class is a unit class when it lies in the image of valuation-ring units. -/
def IsUnitClass (A : ValuationSubring K) (n : ℕ) (x : PowerClass K n) : Prop :=
  x ∈ unitClasses A n

/-- Multiplication by an nth power preserves the power class. -/
@[simp] theorem powerClassMap_pow_mul (n : ℕ) (b q : Kˣ) :
    powerClassMap n (b ^ n * q) = powerClassMap n q := by
  have hb : powerClassMap n (b ^ n) = 1 :=
    (QuotientGroup.eq_one_iff _).mpr ⟨b, rfl⟩
  rw [map_mul, hb, one_mul]

/-- Unit classes have precisely the usual power-times-unit representatives. -/
theorem isUnitClass_iff (A : ValuationSubring K) (n : ℕ) (q : Kˣ) :
    IsUnitClass A n (powerClassMap n q) ↔
      ∃ b : Kˣ, ∃ u : Aˣ, q = b ^ n * Units.map A.subtype.toMonoidHom u := by
  constructor
  · rintro ⟨u, hu⟩
    have heq : (q : PowerClass K n) =
        (Units.map A.subtype.toMonoidHom u : PowerClass K n) := hu.symm
    obtain ⟨b, hb⟩ := QuotientGroup.eq_iff_div_mem.mp heq
    refine ⟨b, u, ?_⟩
    change b ^ n = q / Units.map A.subtype.toMonoidHom u at hb
    rw [hb, div_mul_cancel]
  · rintro ⟨b, u, rfl⟩
    refine ⟨u, ?_⟩
    exact (powerClassMap_pow_mul n b (Units.map A.subtype.toMonoidHom u)).symm

/-- The independent unit predicate agrees with the valuation criterion. -/
theorem isUnitClass_iff_valuation (A : ValuationSubring K) (n : ℕ) (q : Kˣ) :
    IsUnitClass A n (powerClassMap n q) ↔
      ∃ b : Kˣ, A.valuation (q : K) = A.valuation (b : K) ^ n := by
  rw [isUnitClass_iff, A.exists_unit_factor_iff]

/-- Unit membership is invariant under multiplying a parameter by an nth power. -/
theorem isUnitClass_pow_mul_iff (A : ValuationSubring K) (n : ℕ) (b q : Kˣ) :
    IsUnitClass A n (powerClassMap n (b ^ n * q)) ↔
      IsUnitClass A n (powerClassMap n q) := by
  rw [powerClassMap_pow_mul]

end KummerTheory
