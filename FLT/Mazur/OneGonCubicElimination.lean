/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import Mathlib.Tactic.Ring
public import Mathlib.Algebra.Group.Units.Basic

/-!
# Explicit elimination for the self-incidence cubic

A quadratic expression in the three cubic coordinates clears the denominators
of both conductor generators. The formulas work in every characteristic.
-/

@[expose] public section
namespace FLT.Mazur.OneGonCubicElimination
variable {R : Type*} [CommRing R]

/-- A common quadratic denominator for the two conductor generators. -/
def denominator (w c₀ c₁ c₂ : R) : R :=
  -c₀ ^ 2 + 3 * w * c₀ * c₂ + 3 * c₀ * c₁ -
    (3 * w ^ 2 + 3 * w) * c₂ ^ 2 - (3 + 3 * w) * c₁ ^ 2 +
    (1 + w ^ 2 + 2 * w) * c₁ * c₂

/-- The numerator of the conductor t(t-1). -/
def conductorNumerator (w c₀ c₁ c₂ : R) : R :=
  -w * c₀ * c₂ - c₀ * c₁ + (w ^ 2 + w) * c₂ ^ 2 + (1 + w) * c₁ ^ 2

/-- The numerator of the first conductor monomial t²(t-1). -/
def monomialNumerator (w c₀ c₁ c₂ : R) : R :=
  -w * c₀ * c₂ + (1 + w) * c₁ ^ 2

/-- The denominator factors explicitly on the normalization. -/
lemma denominator_parametrization (w z : R) :
    denominator w (1 + w * z ^ 3) z (z ^ 2) = (z - 1) ^ 3 * (1 - w ^ 2 * z ^ 3) := by
  unfold denominator
  ring

/-- The first numerator has the extra factor z(z-1). -/
lemma conductor_parametrization (w z : R) :
    conductorNumerator w (1 + w * z ^ 3) z (z ^ 2) =
      z * (z - 1) * (1 - w ^ 2 * z ^ 3) := by
  unfold conductorNumerator
  ring

/-- The second numerator has the extra factor z². -/
lemma monomial_parametrization (w z : R) :
    monomialNumerator w (1 + w * z ^ 3) z (z ^ 2) = z ^ 2 * (1 - w ^ 2 * z ^ 3) := by
  unfold monomialNumerator
  ring

/-- All three expressions are homogeneous quadratics in the projective ratios. -/
lemma quadratic_scaling (w c₀ c₁ c₂ d : R) :
    denominator w c₀ c₁ c₂ * d ^ 2 = denominator w (c₀ * d) (c₁ * d) (c₂ * d) ∧
    conductorNumerator w c₀ c₁ c₂ * d ^ 2 =
      conductorNumerator w (c₀ * d) (c₁ * d) (c₂ * d) ∧
    monomialNumerator w c₀ c₁ c₂ * d ^ 2 =
      monomialNumerator w (c₀ * d) (c₁ * d) (c₂ * d) := by
  unfold denominator conductorNumerator monomialNumerator
  constructor
  · ring
  constructor <;> ring

/-- The exact generator identities follow from the parametrization and unit denominator. -/
lemma generator_identities (w z d c₀ c₁ c₂ u v : R) (hd : IsUnit d)
    (h₀ : c₀ * d = 1 + w * z ^ 3) (h₁ : c₁ * d = z) (h₂ : c₂ * d = z ^ 2)
    (hu : u * (z - 1) ^ 2 = z) (hv : v * (z - 1) ^ 3 = z ^ 2) :
    u * denominator w c₀ c₁ c₂ = conductorNumerator w c₀ c₁ c₂ ∧
    v * denominator w c₀ c₁ c₂ = monomialNumerator w c₀ c₁ c₂ := by
  obtain ⟨hD, hU, hV⟩ := quadratic_scaling w c₀ c₁ c₂ d
  rw [h₀, h₁, h₂, denominator_parametrization] at hD
  rw [h₀, h₁, h₂, conductor_parametrization] at hU
  rw [h₀, h₁, h₂, monomial_parametrization] at hV
  constructor
  · apply (hd.pow 2).mul_right_cancel
    rw [mul_assoc, hD, hU]
    calc
      _ = (u * (z - 1) ^ 2) * (z - 1) * (1 - w ^ 2 * z ^ 3) := by ring
      _ = _ := by rw [hu]
  · apply (hd.pow 2).mul_right_cancel
    rw [mul_assoc, hD, hV, ← mul_assoc, hv]

end FLT.Mazur.OneGonCubicElimination
