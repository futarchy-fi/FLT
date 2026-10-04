/-
Copyright (c) 2026 krandder. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: krandder
-/
module

public import FLT.PadicHodgeTheory.PadicCyclotomicRootNorm
public import FLT.PadicHodgeTheory.PadicUniformizerOrthogonality

/-! # Uniform coefficient bounds in the cyclotomic uniformizer basis -/

@[expose] public noncomputable section
namespace PadicHodgeTheory
variable (p : ℕ) [hp : Fact p.Prime]

/-- Uniformizer coefficients have a bound independent of the ramification degree. -/
theorem padic_uniformizer_coefficient_le (u : PadicAlgCl p) (e : ℕ)
    (hu : ‖u‖ ^ e = (p : ℝ)⁻¹) (a : Fin e → ℚ_[p]) (i : Fin e) :
    ‖a i‖ ≤ p * ‖∑ j : Fin e, algebraMap ℚ_[p] (PadicAlgCl p) (a j) * u ^ (j : ℕ)‖ := by
  have hp0 : 0 < (p : ℝ) := by exact_mod_cast hp.out.pos
  have hp1 : 1 ≤ (p : ℝ) := by exact_mod_cast hp.out.one_lt.le
  have hu1 : ‖u‖ ≤ 1 := le_of_pow_le_pow_left₀
    (Nat.ne_of_gt (Nat.zero_lt_of_lt i.isLt)) (by positivity)
    (by rw [hu, one_pow]; exact inv_le_one_of_one_le₀ hp1)
  have hui : (p : ℝ)⁻¹ ≤ ‖u‖ ^ (i : ℕ) :=
    hu ▸ pow_le_pow_of_le_one (norm_nonneg _) hu1 i.isLt.le
  have ht := padic_uniformizer_term_le_sum p u e hu a i
  rw [norm_mul, norm_algebraMap, norm_one, mul_one, norm_pow] at ht
  have h := (mul_le_mul_of_nonneg_left hui (norm_nonneg (a i))).trans ht
  calc
    ‖a i‖ = p * (‖a i‖ * (p : ℝ)⁻¹) := by field_simp
    _ ≤ _ := mul_le_mul_of_nonneg_left h hp0.le

/-- Cyclotomic elements have uniformizer expansions with uniformly bounded coefficients. -/
theorem padicCyclotomic_exists_bounded_expansion (s : ℕ) (ζ : PadicAlgCl p)
    (hζ : IsPrimitiveRoot ζ (p ^ (s + 1))) (x : padicCyclotomicTower p (s + 1)) :
    ∃ (d : ℕ) (a : Fin d → ℚ_[p]), d = p ^ s * (p - 1) ∧
      (x : PadicAlgCl p) = ∑ i : Fin d,
        algebraMap ℚ_[p] (PadicAlgCl p) (a i) * (ζ - 1) ^ (i : ℕ) ∧
      ∀ i, ‖a i‖ ≤ p * ‖(x : PadicAlgCl p)‖ := by
  classical
  let : NeZero (p ^ (s + 1)) := ⟨pow_ne_zero _ hp.out.ne_zero⟩
  let z : padicCyclotomicTower p (s + 1) :=
    ⟨ζ, padicCyclotomicTower_root_mem p (s + 1) ζ hζ.pow_eq_one⟩
  have hz : IsPrimitiveRoot z (p ^ (s + 1)) := IsPrimitiveRoot.coe_submonoidClass_iff.mp hζ
  let b := hz.subOnePowerBasis ℚ_[p]
  let a : Fin b.dim → ℚ_[p] := fun i ↦ b.basis.repr x i
  have hd : b.dim = p ^ s * (p - 1) := b.finrank.symm.trans (padicCyclotomicTower_finrank p s)
  have he : (x : PadicAlgCl p) = ∑ i : Fin b.dim,
      algebraMap ℚ_[p] (PadicAlgCl p) (a i) * (ζ - 1) ^ (i : ℕ) := by
    have he := congrArg (padicCyclotomicTower p (s + 1)).val
      (b.basis.sum_repr x)
    simpa only [b.basis_eq_pow, b, IsPrimitiveRoot.subOnePowerBasis_gen,
      map_sum, map_smul, map_pow, map_sub, map_one, Algebra.smul_def, map_mul,
      AlgHom.commutes, a, z, IntermediateField.coe_val] using he.symm
  refine ⟨b.dim, a, hd, he, fun i ↦ ?_⟩
  rw [he]
  exact padic_uniformizer_coefficient_le p (ζ - 1) b.dim
    (hd.symm ▸ padicCyclotomic_sub_one_norm_pow p s ζ hζ) a i

end PadicHodgeTheory
