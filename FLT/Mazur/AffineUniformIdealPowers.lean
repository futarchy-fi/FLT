/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.AffineIdealPowerPullback
public import FLT.Mazur.IdealSheafSupportPower

/-!
# Uniform ideal-power comparisons after arbitrary affine-base pullback

A comparison on a Noetherian affine base gives one linear order bound after
all coefficient changes. The coefficient schemes need not be Noetherian,
reduced, affine, or flat over the base.
-/

@[expose] public noncomputable section
open CategoryTheory AlgebraicGeometry
namespace FLT.Mazur.AffineUniformIdealPowers
open Scheme.IdealSheafData
set_option backward.isDefEq.respectTransparency false
variable {X Y : Scheme.{0}} [IsAffine X]

/-- A single original power inclusion gives linear bounds at every coefficient order. -/
theorem comap_power_le (I J : X.IdealSheafData) {c : ℕ} (h : I ^ c ≤ J)
    (f : Y ⟶ X) (k : ℕ) :
    I.comap f ^ (c * k) ≤ J.comap f ^ k := by
  rw [← AffineIdealPower.comap_pow, ← AffineIdealPower.comap_pow]
  apply comap_mono
  intro U
  change I.ideal U ^ (c * k) ≤ J.ideal U ^ k
  rw [pow_mul]
  exact pow_le_pow_left' (h U) k

variable [IsNoetherian X]

/-- Support containment constructs a bound before any coefficient scheme is chosen. -/
theorem exists_uniform_comap_power_le (I J : X.IdealSheafData)
    (h : J.support ≤ I.support) :
    ∃ c : ℕ, 0 < c ∧ ∀ (Y : Scheme.{0}) (f : Y ⟶ X) (k : ℕ),
      I.comap f ^ (c * k) ≤ J.comap f ^ k := by
  obtain ⟨c, hc⟩ := IdealSheafSupportPower.exists_pow_le_of_support I J h
  exact ⟨c + 1, Nat.succ_pos _, fun _ f k ↦ comap_power_le I J hc f k⟩

/-- Equal support gives both uniform comparisons on the original unreduced coefficients. -/
theorem exists_uniform_comap_comparison (I J : X.IdealSheafData)
    (h : I.support = J.support) :
    ∃ c d : ℕ, 0 < c ∧ 0 < d ∧
      ∀ (Y : Scheme.{0}) (f : Y ⟶ X) (k : ℕ),
        I.comap f ^ (c * k) ≤ J.comap f ^ k ∧
          J.comap f ^ (d * k) ≤ I.comap f ^ k := by
  obtain ⟨c, hc, hIJ⟩ := exists_uniform_comap_power_le I J h.ge
  obtain ⟨d, hd, hJI⟩ := exists_uniform_comap_power_le J I h.le
  exact ⟨c, d, hc, hd, fun Y f k ↦ ⟨hIJ Y f k, hJI Y f k⟩⟩

end FLT.Mazur.AffineUniformIdealPowers
