/-
Copyright (c) 2026 krandder. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: krandder
-/
module

public import FLT.PadicHodgeTheory.PadicCyclotomicCoefficientBound
public import FLT.PadicHodgeTheory.PadicCyclotomicIntegralTrace

/-! # A uniform normalized-trace bound on the actual cyclotomic union -/

@[expose] public noncomputable section
namespace PadicHodgeTheory
variable (p : ℕ) [hp : Fact p.Prime]

/-- The normalized trace bound is independent of both positive target and source level. -/
theorem padicCyclotomicProjection_norm_le (n s : ℕ)
    (x : padicCyclotomicTower p (s + 1)) :
    ‖padicCyclotomicProjection p (n + 1) (x : PadicAlgCl p)‖ ≤ p * ‖(x : PadicAlgCl p)‖ := by
  let : NeZero (p ^ (s + 1)) := ⟨pow_ne_zero _ hp.out.ne_zero⟩
  obtain ⟨ζ, hζ⟩ := HasEnoughRootsOfUnity.exists_primitiveRoot (PadicAlgCl p) (p ^ (s + 1))
  obtain ⟨d, a, _, he, ha⟩ := padicCyclotomic_exists_bounded_expansion p s ζ hζ x
  conv_lhs => rw [he, map_sum]
  apply IsUltrametricDist.norm_sum_le_of_forall_le_of_nonneg
    (mul_nonneg (Nat.cast_nonneg p) (norm_nonneg _))
  intro i _
  have hlin : padicCyclotomicProjection p (n + 1)
      (algebraMap ℚ_[p] (PadicAlgCl p) (a i) * (ζ - 1) ^ (i : ℕ)) =
      algebraMap ℚ_[p] (PadicAlgCl p) (a i) *
        padicCyclotomicProjection p (n + 1) ((ζ - 1) ^ (i : ℕ)) := by
    simpa only [Algebra.smul_def] using
      (padicCyclotomicProjection p (n + 1)).map_smul (a i) ((ζ - 1) ^ (i : ℕ))
  rw [hlin, norm_mul, norm_algebraMap, norm_one, mul_one]
  exact (mul_le_mul_of_nonneg_left
    (padicCyclotomicProjection_uniformizer_pow_norm_le_one p n (s + 1) i ζ hζ.pow_eq_one)
    (norm_nonneg _)).trans (by simpa only [mul_one] using ha i)

/-- The actual union of the finite cyclotomic subfields. -/
def padicCyclotomicUnion : IntermediateField ℚ_[p] (PadicAlgCl p) :=
  ⨆ n : ℕ, padicCyclotomicTower p (n + 1)

/-- Membership in the cyclotomic union means membership in an actual finite level. -/
theorem mem_padicCyclotomicUnion (x : PadicAlgCl p) :
    x ∈ padicCyclotomicUnion p ↔ ∃ n, x ∈ padicCyclotomicTower p (n + 1) := by
  change x ∈ (⨆ n : ℕ, padicCyclotomicTower p (n + 1)).toSubfield ↔ _
  rw [IntermediateField.iSup_toSubfield]
  apply Subfield.mem_iSup_of_directed
  intro n m
  refine ⟨max n m, ?_, ?_⟩
  · exact padicCyclotomicTower_mono p (Nat.add_le_add_right (le_max_left n m) 1)
  · exact padicCyclotomicTower_mono p (Nat.add_le_add_right (le_max_right n m) 1)

/-- The uniform bound holds on the union, without a bound on the element's source level. -/
theorem padicCyclotomicProjection_union_norm_le (n : ℕ) (x : padicCyclotomicUnion p) :
    ‖padicCyclotomicProjection p (n + 1) (x : PadicAlgCl p)‖ ≤ p * ‖(x : PadicAlgCl p)‖ := by
  obtain ⟨s, hs⟩ := (mem_padicCyclotomicUnion p x).mp x.property
  exact padicCyclotomicProjection_norm_le p n s ⟨x, hs⟩

end PadicHodgeTheory
