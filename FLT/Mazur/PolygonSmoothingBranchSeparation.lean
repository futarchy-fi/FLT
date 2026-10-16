/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.PolygonSmoothingFlat
public import FLT.Mazur.PolygonSmoothingOverlapGraph

/-!
# Faithful detection by both full Laurent branches

Although either punctured branch may lose information at a nilpotent
stage, the pair detects every element of the original node ring. The
regular sum coordinate rules out sections supported only at the node.
-/

@[expose] public noncomputable section
open scoped LaurentPolynomial
open Polynomial
namespace FLT.Mazur.PolygonSmoothing
variable {R : Type*} [CommRing R] (t : R)

/-- The original sum of node coordinates is regular over an arbitrary base ring. -/
theorem coordinate_sum_regular : IsRegular (leftCoordinate t + rightCoordinate t) := by
  have hr : IsRegular (sumCoordinate t) := by
    have hx : IsSMulRegular R[X] (Polynomial.X : R[X]) :=
      isLeftRegular_iff.mp Polynomial.isRegular_X.left
    have hs : IsLeftRegular (sumCoordinate t) :=
      isLeftRegular_iff.mpr (IsSMulRegular.of_flat (S := QuadraticModel t) hx)
    exact ⟨hs, by intro a b he; apply hs; simpa only [mul_comm] using he⟩
  constructor
  · intro a b hab
    apply (quadraticEquiv t).injective
    apply hr.left
    have he := congrArg (chartToQuadratic t) hab
    simpa only [map_mul, map_add, chartToQuadratic_left, chartToQuadratic_right,
      sub_add_cancel, quadraticEquiv, AlgEquiv.ofAlgHom_apply] using he
  · intro a b hab
    apply (quadraticEquiv t).injective
    apply hr.right
    have he := congrArg (chartToQuadratic t) hab
    simpa only [map_mul, map_add, chartToQuadratic_left, chartToQuadratic_right,
      sub_add_cancel, quadraticEquiv, AlgEquiv.ofAlgHom_apply] using he

/-- Vanishing on the outgoing Laurent branch is annihilation by a power of x. -/
theorem leftLaurentMap_eq_zero_iff (z : ChartRing t) :
    leftLaurentMap t z = 0 ↔ ∃ k : ℕ, leftCoordinate t ^ k * z = 0 := by
  have he : leftLaurentMap t z = 0 ↔
      algebraMap (ChartRing t) (LeftPuncture t) z = 0 := by
    rw [← leftPunctureToLaurent_map]
    exact map_eq_zero_iff (leftPunctureEquiv t) (leftPunctureEquiv t).injective
  rw [he, ← map_zero (algebraMap (ChartRing t) (LeftPuncture t)),
    IsLocalization.eq_iff_exists (Submonoid.powers (leftCoordinate t))]
  constructor
  · rintro ⟨⟨_, k, rfl⟩, hk⟩
    exact ⟨k, by simpa only [mul_zero, mul_comm] using hk⟩
  · rintro ⟨k, hk⟩
    exact ⟨⟨_, ⟨k, rfl⟩⟩, by simpa only [mul_zero, mul_comm] using hk⟩

/-- Vanishing on the incoming Laurent branch is annihilation by a power of y. -/
theorem precedingLaurentMap_eq_zero_iff (z : ChartRing t) :
    precedingLaurentMap R t z = 0 ↔ ∃ k : ℕ, rightCoordinate t ^ k * z = 0 := by
  change LaurentPolynomial.invert (leftLaurentMap t (branchSwapMap t z)) = 0 ↔ _
  rw [map_eq_zero_iff LaurentPolynomial.invert LaurentPolynomial.invert.injective,
    leftLaurentMap_eq_zero_iff]
  constructor
  · rintro ⟨k, hk⟩
    refine ⟨k, ?_⟩
    have he := congrArg (branchSwap t) hk
    simpa only [map_mul, map_pow, branchSwap, AlgEquiv.ofAlgHom_apply,
      branchSwapMap_left, map_zero, ← AlgHom.comp_apply, branchSwapMap_comp,
      AlgHom.id_apply] using he
  · rintro ⟨k, hk⟩
    refine ⟨k, ?_⟩
    have he := congrArg (branchSwapMap t) hk
    simpa only [map_mul, map_pow, branchSwapMap_right, map_zero] using he

/-- No nonzero original node element vanishes on both full punctured branches. -/
theorem eq_zero_of_both_laurent (z : ChartRing t)
    (hl : leftLaurentMap t z = 0) (hr : precedingLaurentMap R t z = 0) : z = 0 := by
  obtain ⟨a, ha⟩ := (leftLaurentMap_eq_zero_iff t z).mp hl
  obtain ⟨b, hb⟩ := (precedingLaurentMap_eq_zero_iff t z).mp hr
  let J : Ideal (ChartRing t) := LinearMap.ker (LinearMap.mulRight (ChartRing t) z)
  have hx : leftCoordinate t ∈ J.radical := ⟨a, ha⟩
  have hy : rightCoordinate t ∈ J.radical := ⟨b, hb⟩
  obtain ⟨k, hk⟩ := J.radical.add_mem hx hy
  apply ((coordinate_sum_regular t).pow k).left
  exact hk.trans (mul_zero _).symm

/-- Both original Laurent restrictions together determine the full chart element. -/
theorem eq_of_both_laurent (z w : ChartRing t)
    (hl : leftLaurentMap t z = leftLaurentMap t w)
    (hr : precedingLaurentMap R t z = precedingLaurentMap R t w) : z = w := by
  apply sub_eq_zero.mp
  apply eq_zero_of_both_laurent t (z - w)
  · rw [map_sub, hl, sub_self]
  · rw [map_sub, hr, sub_self]

end FLT.Mazur.PolygonSmoothing
