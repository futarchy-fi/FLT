/-
Copyright (c) 2026 krandder. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: krandder
-/
module

public import FLT.Mazur.EllipticStarZeroCoordinates

/-!
# Actual coordinates in the triple-root additive branch

For depths (1,2,2,3,4), the I₀* residual cubic is T³. Every point outside
E₀ therefore has both coordinates divisible by π². The next residual
quadratic has nonzero discriminant when b₆ has exact depth four.
-/

@[expose] public section

namespace FLT.Mazur

open WeierstrassCurve IsLocalRing

/-- Points outside E₀ have coordinates (π²x,π²y) in the triple-root branch. -/
theorem exists_typeIVStarCoordinates {K : Type*} [Field K]
    (A : ValuationSubring K) (W : WeierstrassCurve A) {π : A} (hπ : π ≠ 0)
    (hgen : maximalIdeal A = Ideal.span {π})
    (h1 : W.a₁ ∈ maximalIdeal A) (h2 : W.a₂ ∈ maximalIdeal A ^ 2)
    (h3 : W.a₃ ∈ maximalIdeal A ^ 2) (h4 : W.a₄ ∈ maximalIdeal A ^ 3)
    (h6 : W.a₆ ∈ maximalIdeal A ^ 4)
    (P : (W.map (algebraMap A K)).toProjective.Point) (hP : ¬ SmoothReduction A W P) :
    Nonempty (TypeIVCoordinates A W (π ^ 2) P) := by
  obtain ⟨e2, he2m, he2⟩ := exists_node_deep_factor hgen 1 h2
  obtain ⟨e3, he3⟩ := exists_node_coordinate_factor hgen 2 h3
  obtain ⟨e4, he4m, he4⟩ := exists_node_deep_factor hgen 2 h4
  obtain ⟨e6, he6m, he6⟩ := exists_node_deep_factor hgen 3 h6
  simp only [pow_one] at he2
  have hπm : π ∈ maximalIdeal A := hgen ▸ Ideal.mem_span_singleton_self π
  obtain ⟨v⟩ := exists_starZeroCoordinates A W hπ hgen e3 e4 e6 h1
    (Ideal.pow_le_self (by decide : 2 ≠ 0) h2) he3 he4 he6 P hP
  have hr := starZero_scaled_residue W hπ hπm v.x v.y e2 e3 e4 e6 h1
    he2 he3 he4 he6 v.equation
  have hx : residue A v.x ^ 3 = 0 := by
    simpa only [(residue_eq_zero_iff _).mpr he2m, (residue_eq_zero_iff _).mpr he4m,
      (residue_eq_zero_iff _).mpr he6m, zero_mul, add_zero] using hr
  have hxm := (residue_eq_zero_iff _).mp
    ((pow_eq_zero_iff (by decide : 3 ≠ 0)).mp hx)
  obtain ⟨a, ha⟩ := exists_node_coordinate_factor hgen 1 (by simpa using hxm)
  simp only [pow_one] at ha
  have he : π * v.x = π ^ 2 * a := by rw [ha]; ring
  have hn : (W.map (algebraMap A K)).toAffine.Nonsingular
      ((π ^ 2 * a : A) : K) ((π ^ 2 * v.y : A) : K) := by
    simpa only [he] using v.nonsingular
  refine ⟨⟨a, v.y, hn, v.represents.trans ?_⟩⟩
  apply congrArg Affine.Point.toProjective
  simp only [Affine.Point.some.injEq]
  exact ⟨congrArg Subtype.val he, True.intro⟩

/-- Exact depth four of b₆ gives distinct roots of the later residual quadratic. -/
theorem typeIVStar_residue_discriminant_ne_zero {R : Type*} [CommRing R] [IsLocalRing R]
    (W : WeierstrassCurve R) {π : R} (hπm : π ∈ maximalIdeal R)
    (e3 e6 : R) (h3 : W.a₃ = π ^ 2 * e3) (h6 : W.a₆ = π ^ 4 * e6)
    (hb6 : W.b₆ ∉ maximalIdeal R ^ 5) : residue R e3 ^ 2 + 4 * residue R e6 ≠ 0 := by
  intro hz
  have hm : e3 ^ 2 + 4 * e6 ∈ maximalIdeal R :=
    (residue_eq_zero_iff _).mp (by simpa only [map_add, map_pow, map_mul, map_ofNat] using hz)
  apply hb6
  have hb : W.b₆ = π ^ 4 * (e3 ^ 2 + 4 * e6) := by rw [b₆, h3, h6]; ring
  rw [hb, pow_succ]
  exact Ideal.mul_mem_mul (Ideal.pow_mem_pow hπm 4) hm

end FLT.Mazur
