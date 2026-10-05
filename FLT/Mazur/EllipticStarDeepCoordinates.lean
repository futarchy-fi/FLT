/-
Copyright (c) 2026 krandder. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: krandder
-/
module

public import FLT.Mazur.EllipticTypeIVStarCoordinates

/-!
# Coordinates after the type IV* branch

When a₃ has depth three and a₆ depth five, the later residual quadratic
is T². Hence an actual point outside E₀ has coordinates (π²x,π³y).
-/

@[expose] public section

namespace FLT.Mazur

open WeierstrassCurve IsLocalRing

variable {K : Type*} [Field K] (A : ValuationSubring K) (W : WeierstrassCurve A)

/-- Actual divided coordinates for the III* and II* branches. -/
structure StarDeepCoordinates (π : A) (P : (W.map (algebraMap A K)).toProjective.Point) where
  /-- The x-coordinate divided by π². -/
  x : A
  /-- The y-coordinate divided by π³. -/
  y : A
  nonsingular : (W.map (algebraMap A K)).toAffine.Nonsingular
    ((π ^ 2 * x : A) : K) ((π ^ 3 * y : A) : K)
  represents : P = Affine.Point.toProjective (.some _ _ nonsingular)

/-- The vanished later residual quadratic forces y to have depth three. -/
theorem exists_starDeepCoordinates {π : A} (hπ : π ≠ 0)
    (hgen : maximalIdeal A = Ideal.span {π})
    (h1 : W.a₁ ∈ maximalIdeal A) (h2 : W.a₂ ∈ maximalIdeal A ^ 2)
    (h3 : W.a₃ ∈ maximalIdeal A ^ 3) (h4 : W.a₄ ∈ maximalIdeal A ^ 3)
    (h6 : W.a₆ ∈ maximalIdeal A ^ 5)
    (P : (W.map (algebraMap A K)).toProjective.Point) (hP : ¬ SmoothReduction A W P) :
    Nonempty (StarDeepCoordinates A W π P) := by
  obtain ⟨v⟩ := exists_typeIVStarCoordinates A W hπ hgen h1 h2
    (Ideal.pow_le_pow_right (by decide : 2 ≤ 3) h3) h4
    (Ideal.pow_le_pow_right (by decide : 4 ≤ 5) h6) P hP
  obtain ⟨e3, he3m, he3⟩ := exists_node_deep_factor hgen 2 h3
  obtain ⟨e4, he4m, he4⟩ := exists_node_deep_factor hgen 2 h4
  obtain ⟨e6, he6m, he6⟩ := exists_node_deep_factor hgen 4 h6
  have hπm : π ∈ maximalIdeal A := hgen ▸ Ideal.mem_span_singleton_self π
  have hr := typeIV_scaled_residue W (pow_ne_zero 2 hπ)
    (Ideal.pow_le_self (by decide : 2 ≠ 0) (Ideal.pow_mem_pow hπm 2))
    v.x v.y e3 e4 e6 h1 (Ideal.pow_le_self (by decide : 2 ≠ 0) h2) he4m he3 he4
    (by simpa only [← pow_mul] using he6) v.equation
  have hy : residue A v.y ^ 2 = 0 := by
    simpa only [(residue_eq_zero_iff _).mpr he3m, (residue_eq_zero_iff _).mpr he6m,
      zero_mul, add_zero] using hr
  have hym := (residue_eq_zero_iff _).mp
    ((pow_eq_zero_iff (by decide : 2 ≠ 0)).mp hy)
  obtain ⟨b, hb⟩ := exists_node_coordinate_factor hgen 1 (by simpa using hym)
  simp only [pow_one] at hb
  have he : π ^ 2 * v.y = π ^ 3 * b := by rw [hb]; ring
  have hn : (W.map (algebraMap A K)).toAffine.Nonsingular
      ((π ^ 2 * v.x : A) : K) ((π ^ 3 * b : A) : K) := by
    simpa only [he] using v.nonsingular
  refine ⟨⟨v.x, b, hn, v.represents.trans ?_⟩⟩
  apply congrArg Affine.Point.toProjective
  simp only [Affine.Point.some.injEq]
  exact ⟨True.intro, congrArg Subtype.val he⟩

variable {A W} {π : A} {P : (W.map (algebraMap A K)).toProjective.Point}

/-- The integral coordinates satisfy the original equation. -/
theorem StarDeepCoordinates.equation (v : StarDeepCoordinates A W π P) :
    W.toAffine.Equation (π ^ 2 * v.x) (π ^ 3 * v.y) :=
  (W.toAffine.map_equation (IsFractionRing.injective A K) _ _).mp v.nonsingular.1

end FLT.Mazur
