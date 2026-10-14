/-
Copyright (c) 2026 krandder. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: krandder
-/
module

public import FLT.Mazur.WeierstrassDilatationResidueDepth
public import FLT.Mazur.WeierstrassDilatationCoefficients

/-!
# Integral sections avoid the terminal node at odd final depth

When the remaining constant coefficient has exact order one, an integral
solution cannot have both coordinates in the maximal ideal. This is an
arithmetic restriction on actual sections, not a smoothness assumption.
-/

@[expose] public noncomputable section
open IsLocalRing
namespace FLT.Mazur.WeierstrassDilatation
variable {R : Type*} [CommRing R] [IsDomain R] [IsLocalRing R]
  {W : WeierstrassCurve R} {π : R} {depth : ℕ} (D : SplitNodeDepth W π depth)
  (k : ℕ) (hk : depth = 2 * k + 1) (b3 b4 b6 : R)
  (h3 : W.a₃ = π ^ k * b3) (h4 : W.a₄ = π ^ k * b4)
  (h6 : W.a₆ = (π ^ k) ^ 2 * b6)

omit [IsDomain R] in
include D hk h6 in
/-- At odd final depth the divided constant has exact maximal-ideal order one. -/
theorem divided_constant_not_mem_square : b6 ∉ maximalIdeal R ^ 2 := by
  intro hb
  apply D.a₆_not_mem
  have hp : π ^ (2 * k) ∈ maximalIdeal R ^ (2 * k) := by
    rw [D.maximalIdeal_eq, Ideal.span_singleton_pow]
    exact Ideal.subset_span (Set.mem_singleton _)
  have hm := Ideal.mul_mem_mul hp hb
  rw [← pow_add] at hm
  simpa only [h6, ← pow_mul, Nat.mul_comm k 2, hk, Nat.add_assoc] using hm

include D hk h3 h4 h6 in
/-- Every actual integral solution is primitive at the odd terminal divided depth. -/
theorem divided_solution_primitive_odd (a b : R)
    (he : b ^ 2 + (W.a₁ * a + b3) * b =
      π ^ k * a ^ 3 + W.a₂ * a ^ 2 + b4 * a + b6) : IsUnit a ∨ IsUnit b := by
  by_contra hn
  obtain ⟨ha, hb⟩ := not_or.mp hn
  have ha' : a ∈ maximalIdeal R := ha
  have hb' : b ∈ maximalIdeal R := hb
  obtain ⟨hb3, hb4⟩ := divided_linear_mem D k (by omega) b3 b4 h3 h4
  have ha2 : a ^ 2 ∈ maximalIdeal R ^ 2 := Ideal.pow_mem_pow ha' 2
  have hb2 : b ^ 2 ∈ maximalIdeal R ^ 2 := Ideal.pow_mem_pow hb' 2
  have ha3 : a ^ 3 ∈ maximalIdeal R ^ 2 := by
    simpa only [pow_succ] using (maximalIdeal R ^ 2).mul_mem_right a ha2
  have hmul {u v : R} (hu : u ∈ maximalIdeal R) (hv : v ∈ maximalIdeal R) :
      u * v ∈ maximalIdeal R ^ 2 := by
    simpa only [pow_two] using Ideal.mul_mem_mul hu hv
  have hl : b ^ 2 + (W.a₁ * a + b3) * b ∈ maximalIdeal R ^ 2 :=
    (maximalIdeal R ^ 2).add_mem hb2
      (hmul ((maximalIdeal R).add_mem
        ((maximalIdeal R).mul_mem_left W.a₁ ha') hb3) hb')
  have hr : π ^ k * a ^ 3 + W.a₂ * a ^ 2 + b4 * a ∈ maximalIdeal R ^ 2 :=
    (maximalIdeal R ^ 2).add_mem
      ((maximalIdeal R ^ 2).add_mem ((maximalIdeal R ^ 2).mul_mem_left _ ha3)
        ((maximalIdeal R ^ 2).mul_mem_left _ ha2)) (hmul hb4 ha')
  apply divided_constant_not_mem_square D k hk b6 h6
  have hc : b6 = (b ^ 2 + (W.a₁ * a + b3) * b) -
      (π ^ k * a ^ 3 + W.a₂ * a ^ 2 + b4 * a) := by linear_combination -he
  rw [hc]
  exact (maximalIdeal R ^ 2).sub_mem hl hr

include D hk h3 h4 h6 in
/-- Every section of the terminal divided algebra has a nonvanishing residue coordinate. -/
theorem divided_section_avoids_odd_node
    (f : Coordinate W (π ^ k) b3 b4 b6 →ₐ[R] R) :
    residue R (f (x W (π ^ k) b3 b4 b6)) ≠ 0 ∨
      residue R (f (y W (π ^ k) b3 b4 b6)) ≠ 0 := by
  have he := equation_map W (π ^ k) b3 b4 b6 f
  simp only [Algebra.algebraMap_self, RingHom.id_apply] at he
  rcases divided_solution_primitive_odd D k hk b3 b4 b6 h3 h4 h6 _ _ he with hx | hy
  · exact Or.inl ((residue_ne_zero_iff_isUnit _).mpr hx)
  · exact Or.inr ((residue_ne_zero_iff_isUnit _).mpr hy)

end FLT.Mazur.WeierstrassDilatation
