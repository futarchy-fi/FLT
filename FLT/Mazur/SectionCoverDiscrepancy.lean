/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.SectionCoverCoordinates

/-!
# Killing discrepancies on affine section covers

Local numerators agree over the original section chart. A single further
power of its coordinate kills all discrepancies on the finite affine overlaps.
-/

@[expose] public noncomputable section
open CategoryTheory AlgebraicGeometry
universe u v
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
namespace FLT.Mazur.FCurve.SectionCover
variable {X : Scheme.{u}} {L : X.Modules} {ι : Type v}
variable (s : ι → Γ(L, ⊤))

/-- Numerator discrepancies vanish on every triple overlap with the original chart. -/
lemma discrepancy_vanishes (N : ℕ) (b : ∀ j, Γ(X, chart s j)) (i : ι)
    (a : Γ(X, chart s i))
    (hb : ∀ j, res inf_le_left (b j) =
      ratio s j i (chart s j ⊓ chart s i) inf_le_left ^ N * res inf_le_right a)
    (j k : ι) :
    res (show (chart s j ⊓ chart s k) ⊓ chart s i ≤ _ from inf_le_left)
      (discrepancy s N b j k) = 0 := by
  let V := (chart s j ⊓ chart s k) ⊓ chart s i
  have he (q : ι) (hq : V ≤ chart s q) :
      res hq (b q) = ratio s q i V hq ^ N * res (show V ≤ chart s i from inf_le_right) a := by
    have e := congrArg (res (show V ≤ chart s q ⊓ chart s i from le_inf hq inf_le_right)) (hb q)
    simpa only [map_mul, map_pow, res_ratio, res_res] using e
  simp only [discrepancy, map_sub, map_mul, map_pow, res_ratio, res_res]
  rw [he j (inf_le_left.trans inf_le_left), he k (inf_le_left.trans inf_le_right)]
  rw [← mul_assoc, ← mul_pow, ratio_mul, sub_self]

/-- A uniform further power annihilates all pair discrepancies. -/
theorem kill_discrepancies [Finite ι] (h : ∀ j, IsAffineOpen (chart s j))
    (N : ℕ) (b : ∀ j, Γ(X, chart s j)) (i : ι) (a : Γ(X, chart s i))
    (hb : ∀ j, res inf_le_left (b j) =
      ratio s j i (chart s j ⊓ chart s i) inf_le_left ^ N * res inf_le_right a) :
    ∃ m : ℕ, ∀ j k,
      ratio s j i (chart s j ⊓ chart s k) inf_le_left ^ m * discrepancy s N b j k = 0 := by
  obtain ⟨m, hm⟩ := AffineOpenDenominators.finite_kernels
    (fun p : ι × ι ↦ chart s p.1 ⊓ chart s p.2)
    (fun p : ι × ι ↦ (chart s p.1 ⊓ chart s p.2) ⊓ chart s i)
    (fun p ↦ isAffineOpen_inf s h p.1 p.2)
    (fun p ↦ ratio s p.1 i _ inf_le_left) (fun p ↦ discrepancy s N b p.1 p.2)
    (fun p ↦ inf_eq_basicOpen s p.1 i _ inf_le_left)
    (fun p ↦ discrepancy_vanishes s N b i a hb p.1 p.2)
  exact ⟨m, fun j k ↦ hm (j, k)⟩

/-- Raising the degree scales its discrepancy by the matching coordinate power. -/
lemma discrepancy_corrected (N m : ℕ) (b : ∀ j, Γ(X, chart s j)) (i j k : ι) :
    discrepancy s (N + m) (fun j ↦ ratio s j i (chart s j) le_rfl ^ m * b j) j k =
      ratio s j i (chart s j ⊓ chart s k) inf_le_left ^ m * discrepancy s N b j k := by
  simp only [discrepancy, map_mul, map_pow, res_ratio]
  rw [← ratio_mul s j k i _ inf_le_left inf_le_right]
  rw [mul_pow, pow_add]
  ring

/-- Corrected numerators glue in the transition coordinates of a tensor power. -/
theorem compatible_numerators [Finite ι] (h : ∀ j, IsAffineOpen (chart s j))
    (i : ι) (a : Γ(X, chart s i)) :
    ∃ (N : ℕ) (b : ∀ j, Γ(X, chart s j)),
      (∀ j, res inf_le_left (b j) =
        ratio s j i (chart s j ⊓ chart s i) inf_le_left ^ N * res inf_le_right a) ∧
      ∀ j k, discrepancy s N b j k = 0 := by
  obtain ⟨N, b, hb⟩ := chart_numerators s h i a
  obtain ⟨m, hm⟩ := kill_discrepancies s h N b i a hb
  refine ⟨N + m, fun j ↦ ratio s j i (chart s j) le_rfl ^ m * b j, ?_, ?_⟩
  · intro j
    simp only [map_mul, map_pow, res_ratio, hb j]
    rw [← mul_assoc, ← pow_add, Nat.add_comm m N]
  · intro j k
    rw [discrepancy_corrected]
    exact hm j k

/-- Compatible coefficients can be raised to every larger exponent. -/
theorem eventually_compatible_numerators [Finite ι] (h : ∀ j, IsAffineOpen (chart s j))
    (i : ι) (a : Γ(X, chart s i)) :
    ∃ N : ℕ, ∀ D ≥ N, ∃ b : ∀ j, Γ(X, chart s j),
      (∀ j, res inf_le_left (b j) =
        ratio s j i (chart s j ⊓ chart s i) inf_le_left ^ D * res inf_le_right a) ∧
      ∀ j k, discrepancy s D b j k = 0 := by
  obtain ⟨N, b, hb, hc⟩ := compatible_numerators s h i a
  refine ⟨N, fun D hD ↦ ?_⟩
  have he : N + (D - N) = D := Nat.add_sub_of_le hD
  refine ⟨fun j ↦ ratio s j i (chart s j) le_rfl ^ (D - N) * b j, ?_, ?_⟩
  · intro j
    simp only [map_mul, map_pow, res_ratio, hb j]
    rw [← mul_assoc, ← pow_add, Nat.sub_add_cancel hD]
  · intro j k
    have hcorr := discrepancy_corrected s N (D - N) b i j k
    rw [he, hc j k, mul_zero] at hcorr
    exact hcorr

end FLT.Mazur.FCurve.SectionCover
