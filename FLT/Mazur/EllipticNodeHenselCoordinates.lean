/-
Copyright (c) 2026 krandder. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: krandder
-/
module

public import FLT.Mazur.EllipticNodeComponentLabel
public import FLT.Mazur.HenselianSmallCubic

/-!
# Lifting primitive depth-one nodal coordinates

Hensel's lemma supplies integral solutions of the actual Weierstrass equation.
At depth at least three, fix x = π and lift the first tangent branch. At depth
two, fix y = π and solve a cubic with unit linear coefficient.
-/

@[expose] public section

namespace FLT.Mazur

open IsLocalRing WeierstrassCurve

variable {R : Type*} [CommRing R] [IsLocalRing R]
  [HenselianRing R (maximalIdeal R)] {W : WeierstrassCurve R} {π : R} {n : ℕ}

/-- For depth at least three, the first tangent lifts with divided x-coordinate one. -/
theorem exists_node_first_hensel_coordinates (D : SplitNodeDepth W π n) (hn : 3 ≤ n) :
    ∃ b : R, b ∈ maximalIdeal R ∧ W.toAffine.Equation π (π * b) := by
  obtain ⟨e₃, hm₃, he₃⟩ := exists_node_deep_factor D.maximalIdeal_eq 1
    (Ideal.pow_le_pow_right (by omega) D.a₃_mem)
  obtain ⟨e₄, hm₄, he₄⟩ := exists_node_deep_factor D.maximalIdeal_eq 1
    (Ideal.pow_le_pow_right (by omega) D.a₄_mem)
  obtain ⟨e₆, hm₆, he₆⟩ := exists_node_deep_factor D.maximalIdeal_eq 2
    (Ideal.pow_le_pow_right hn D.a₆_mem)
  simp only [pow_one] at he₃ he₄
  let f : Polynomial R := Polynomial.X ^ 2 + Polynomial.C (W.a₁ + e₃) * Polynomial.X -
    Polynomial.C (π + W.a₂ + e₄ + e₆)
  have hf : f.Monic := by unfold f; monicity <;> norm_num
  have hπ : π ∈ maximalIdeal R := D.maximalIdeal_eq ▸ Ideal.mem_span_singleton_self π
  have h0 : f.eval 0 ∈ maximalIdeal R := by
    simpa [f] using (maximalIdeal R).neg_mem
      ((maximalIdeal R).add_mem ((maximalIdeal R).add_mem
        ((maximalIdeal R).add_mem hπ D.a₂_mem) hm₄) hm₆)
  have hu : IsUnit (Ideal.Quotient.mk (maximalIdeal R) (f.derivative.eval 0)) := by
    change IsUnit (residue R (f.derivative.eval 0))
    simpa [f, Polynomial.derivative_pow, Polynomial.derivative_mul,
      (residue_eq_zero_iff _).mpr hm₃] using D.a₁_unit.map (residue R)
  obtain ⟨b, hb, hm⟩ := HenselianRing.is_henselian f hf 0 h0 hu
  refine ⟨b, by simpa using hm, ?_⟩
  have he : b ^ 2 + (W.a₁ + e₃) * b - (π + W.a₂ + e₄ + e₆) = 0 := by
    simpa [Polynomial.IsRoot, f] using hb
  rw [Affine.equation_iff, he₃, he₄, he₆]
  linear_combination π ^ 2 * he

/-- At depth two, divided y-coordinate one lifts by the small-cubic lemma. -/
theorem exists_node_middle_hensel_coordinates (D : SplitNodeDepth W π 2) :
    ∃ a : R, W.toAffine.Equation (π * a) π := by
  obtain ⟨e₃, _, he₃⟩ := exists_node_deep_factor D.maximalIdeal_eq 1
    (Ideal.pow_le_pow_right (by omega) D.a₃_mem)
  obtain ⟨e₄, hm₄, he₄⟩ := exists_node_deep_factor D.maximalIdeal_eq 1
    (Ideal.pow_le_pow_right (by omega) D.a₄_mem)
  obtain ⟨e₆, he₆⟩ := exists_node_coordinate_factor D.maximalIdeal_eq 2 D.a₆_mem
  simp only [pow_one] at he₃ he₄
  have hu : IsUnit (e₄ - W.a₁) := by
    apply (residue_ne_zero_iff_isUnit _).mp
    simpa [(residue_eq_zero_iff _).mpr hm₄] using
      neg_ne_zero.mpr ((residue_ne_zero_iff_isUnit _).mpr D.a₁_unit)
  obtain ⟨a, ha⟩ := exists_root_small_cubic π W.a₂ (e₄ - W.a₁) (e₆ - 1 - e₃)
    (D.maximalIdeal_eq ▸ Ideal.mem_span_singleton_self π) D.a₂_mem hu
  refine ⟨a, ?_⟩
  rw [Affine.equation_iff, he₃, he₄, he₆]
  linear_combination -π ^ 2 * ha

end FLT.Mazur
