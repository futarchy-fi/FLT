/-
Copyright (c) 2026 krandder. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: krandder
-/
module

public import FLT.Mazur.EllipticDoubleRootEvenCoordinates

/-!
# Coordinate induction along the double-root branch with a₆ = 0

When both residual tests vanish, the even quadratic is (a₂/π)T².
Its nonzero leading coefficient forces the next x-depth. Induction shows
that every nonsmooth point is over the original simple cubic root or has
actual coordinates in the current deeper chart.
-/

@[expose] public section

namespace FLT.Mazur

open WeierstrassCurve IsLocalRing

variable {K : Type*} [Field K] {A : ValuationSubring K} {W : WeierstrassCurve A}
  {π : A} {k : ℕ} {P : (W.map (algebraMap A K)).toProjective.Point}

/-- Vanishing of the even quadratic deepens x into the next odd chart. -/
theorem DoubleRootEvenCoordinates.exists_next
    (v : DoubleRootEvenCoordinates A W π k P) (hπ : π ≠ 0)
    (hgen : maximalIdeal A = Ideal.span {π}) (e2 : A)
    (h1 : W.a₁ ∈ maximalIdeal A) (h2 : W.a₂ = π * e2) (h2m : e2 ∉ maximalIdeal A)
    (h3 : W.a₃ ∈ maximalIdeal A ^ (k + 3))
    (h4 : W.a₄ ∈ maximalIdeal A ^ (k + 4)) (h6 : W.a₆ = 0) :
    Nonempty (TypeIVCoordinates A W (π ^ (k + 3)) P) := by
  obtain ⟨e3, he3⟩ := exists_node_coordinate_factor hgen (k + 3) h3
  obtain ⟨e4, he4m, he4⟩ := exists_node_deep_factor hgen (k + 3) h4
  have hr := doubleRoot_even_scaled_residue W hπ
    (hgen ▸ Ideal.mem_span_singleton_self π) k v.x v.y e2 e3 e4 0 h1 h2 he3 he4
    (by simp [h6]) v.equation
  have hx : residue A v.x = 0 := by
    simp only [(residue_eq_zero_iff _).mpr he4m, map_zero, zero_mul, add_zero] at hr
    exact (pow_eq_zero_iff (by decide : 2 ≠ 0)).mp
      ((mul_eq_zero.mp hr).resolve_left (fun h => h2m ((residue_eq_zero_iff _).mp h)))
  obtain ⟨a, ha⟩ := exists_node_coordinate_factor hgen 1
    (by simpa using (residue_eq_zero_iff _).mp hx)
  simp only [pow_one] at ha
  have he : π ^ (k + 2) * v.x = π ^ (k + 3) * a := by rw [ha, pow_succ]; ring
  have hn : (W.map (algebraMap A K)).toAffine.Nonsingular
      ((π ^ (k + 3) * a : A) : K) ((π ^ (k + 3) * v.y : A) : K) := by
    simpa only [he] using v.nonsingular
  refine ⟨⟨a, v.y, hn, v.represents.trans ?_⟩⟩
  apply congrArg Affine.Point.toProjective
  simp only [Affine.Point.some.injEq]
  exact ⟨congrArg Subtype.val he, True.intro⟩

/-- At every depth, actual nonsmooth points lie over the simple root or in the deeper chart. -/
theorem doubleRoot_simple_or_deep_coordinates (A : ValuationSubring K) (W : WeierstrassCurve A)
    {π : A} (hπ : π ≠ 0) (hgen : maximalIdeal A = Ideal.span {π}) (e2 : A)
    (h1 : W.a₁ ∈ maximalIdeal A) (h2 : W.a₂ = π * e2) (h2m : e2 ∉ maximalIdeal A)
    (k : ℕ) (h3 : W.a₃ ∈ maximalIdeal A ^ (k + 2))
    (h4 : W.a₄ ∈ maximalIdeal A ^ (k + 3)) (h6 : W.a₆ = 0)
    (P : (W.map (algebraMap A K)).toProjective.Point) (hP : ¬ SmoothReduction A W P) :
    (∃ v : StarZeroCoordinates A W π P, residue A v.x = -residue A e2) ∨
      Nonempty (TypeIVCoordinates A W (π ^ (k + 2)) P) := by
  have hπm : π ∈ maximalIdeal A := hgen ▸ Ideal.mem_span_singleton_self π
  have h2' : W.a₂ ∈ maximalIdeal A := h2 ▸ (maximalIdeal A).mul_mem_right _ hπm
  induction k with
  | zero =>
    obtain ⟨e3, he3⟩ := exists_node_coordinate_factor hgen 2 h3
    obtain ⟨e4, he4m, he4⟩ := exists_node_deep_factor hgen 2 h4
    have he6 : W.a₆ = π ^ 3 * 0 := by simp [h6]
    obtain ⟨v⟩ := exists_starZeroCoordinates A W hπ hgen e3 e4 0 h1 h2' he3 he4 he6 P hP
    rcases v.doubleRoot_label hπ hπm e2 e3 e4 0 h1 h2 he3 he4 he6 he4m
        (maximalIdeal A).zero_mem with hx | hx
    · exact Or.inr (v.exists_doubleRootCoordinates hgen hx)
    · exact Or.inl ⟨v, hx⟩
  | succ k ih =>
    rcases ih (Ideal.pow_le_pow_right (by omega) h3)
        (Ideal.pow_le_pow_right (by omega) h4) with hs | hv
    · exact Or.inl hs
    · obtain ⟨v⟩ := hv
      obtain ⟨w⟩ := v.exists_doubleRootEvenCoordinates hπ hgen h1 h2' h3
        (Ideal.pow_le_pow_right (by omega) h4) (by simp [h6])
      exact Or.inr (w.exists_next hπ hgen e2 h1 h2 h2m h3 h4 h6)

end FLT.Mazur
