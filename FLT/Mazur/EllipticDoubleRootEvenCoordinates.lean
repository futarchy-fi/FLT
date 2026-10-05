/-
Copyright (c) 2026 krandder. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: krandder
-/
module

public import FLT.Mazur.EllipticDoubleRootCoordinates

/-!
# The even charts of the double-root iteration

At stage k the actual coordinates are (π^(k+2)x, π^(k+3)y).
The divided equation gives a quadratic in x with leading coefficient a₂/π.
A vanished odd-stage y-quadratic constructs these coordinates from actual
points, with no assumed component labels.
-/

@[expose] public section

namespace FLT.Mazur

open WeierstrassCurve IsLocalRing

/-- Divide the even-chart equation by π^(2k+5). -/
theorem doubleRoot_even_scaled_equation {R : Type*} [CommRing R] [IsDomain R]
    (W : WeierstrassCurve R) {π : R} (hπ : π ≠ 0) (k : ℕ) (x y e2 e3 e4 e6 : R)
    (h2 : W.a₂ = π * e2) (h3 : W.a₃ = π ^ (k + 3) * e3)
    (h4 : W.a₄ = π ^ (k + 3) * e4) (h6 : W.a₆ = π ^ (2 * k + 5) * e6)
    (he : W.toAffine.Equation (π ^ (k + 2) * x) (π ^ (k + 3) * y)) :
    π * y ^ 2 + W.a₁ * x * y + π * e3 * y =
      π ^ (k + 1) * x ^ 3 + e2 * x ^ 2 + e4 * x + e6 := by
  apply mul_left_cancel₀ (pow_ne_zero (2 * k + 5) hπ)
  have he' := (Affine.equation_iff _ _).mp he
  rw [h2, h3, h4, h6] at he'
  simp only [pow_add, pow_mul] at he' ⊢
  linear_combination he'

/-- The divided x-coordinate satisfies the even residual quadratic. -/
theorem doubleRoot_even_scaled_residue {R : Type*} [CommRing R] [IsDomain R]
    [IsLocalRing R] (W : WeierstrassCurve R) {π : R} (hπ : π ≠ 0)
    (hπm : π ∈ maximalIdeal R) (k : ℕ) (x y e2 e3 e4 e6 : R)
    (h1 : W.a₁ ∈ maximalIdeal R) (h2 : W.a₂ = π * e2)
    (h3 : W.a₃ = π ^ (k + 3) * e3) (h4 : W.a₄ = π ^ (k + 3) * e4)
    (h6 : W.a₆ = π ^ (2 * k + 5) * e6)
    (he : W.toAffine.Equation (π ^ (k + 2) * x) (π ^ (k + 3) * y)) :
    residue R e2 * residue R x ^ 2 + residue R e4 * residue R x + residue R e6 = 0 := by
  have h := congrArg (residue R)
    (doubleRoot_even_scaled_equation W hπ k x y e2 e3 e4 e6 h2 h3 h4 h6 he)
  simpa [(residue_eq_zero_iff _).mpr hπm, (residue_eq_zero_iff _).mpr h1] using h.symm

variable {K : Type*} [Field K] (A : ValuationSubring K) (W : WeierstrassCurve A)

/-- Actual affine coordinates in an even double-root chart. -/
structure DoubleRootEvenCoordinates (π : A) (k : ℕ)
    (P : (W.map (algebraMap A K)).toProjective.Point) where
  /-- The x-coordinate divided by π^(k+2). -/
  x : A
  /-- The y-coordinate divided by π^(k+3). -/
  y : A
  nonsingular : (W.map (algebraMap A K)).toAffine.Nonsingular
    ((π ^ (k + 2) * x : A) : K) ((π ^ (k + 3) * y : A) : K)
  represents : P = Affine.Point.toProjective (.some _ _ nonsingular)

variable {A W} {π : A} {k : ℕ} {P : (W.map (algebraMap A K)).toProjective.Point}

/-- The even coordinates satisfy the original integral equation. -/
theorem DoubleRootEvenCoordinates.equation (v : DoubleRootEvenCoordinates A W π k P) :
    W.toAffine.Equation (π ^ (k + 2) * v.x) (π ^ (k + 3) * v.y) :=
  (W.toAffine.map_equation (IsFractionRing.injective A K) _ _).mp v.nonsingular.1

/-- Vanishing of the odd residual quadratic deepens the actual y-coordinate. -/
theorem TypeIVCoordinates.exists_doubleRootEvenCoordinates
    (v : TypeIVCoordinates A W (π ^ (k + 2)) P) (hπ : π ≠ 0)
    (hgen : maximalIdeal A = Ideal.span {π})
    (h1 : W.a₁ ∈ maximalIdeal A) (h2 : W.a₂ ∈ maximalIdeal A)
    (h3 : W.a₃ ∈ maximalIdeal A ^ (k + 3))
    (h4 : W.a₄ ∈ maximalIdeal A ^ (k + 3))
    (h6 : W.a₆ ∈ maximalIdeal A ^ (2 * (k + 2) + 1)) :
    Nonempty (DoubleRootEvenCoordinates A W π k P) := by
  obtain ⟨e3, he3m, he3⟩ := exists_node_deep_factor hgen (k + 2) h3
  obtain ⟨e4, he4m, he4⟩ := exists_node_deep_factor hgen (k + 2) h4
  obtain ⟨e6, he6m, he6⟩ := exists_node_deep_factor hgen (2 * (k + 2)) h6
  have hπm : π ∈ maximalIdeal A := hgen ▸ Ideal.mem_span_singleton_self π
  have hr := typeIV_scaled_residue W (pow_ne_zero (k + 2) hπ)
    (Ideal.pow_le_self (by omega : k + 2 ≠ 0) (Ideal.pow_mem_pow hπm (k + 2)))
    v.x v.y e3 e4 e6 h1 h2 he4m he3 he4
    (by simpa only [← pow_mul, Nat.mul_comm] using he6) v.equation
  have hy : residue A v.y ^ 2 = 0 := by
    simpa only [(residue_eq_zero_iff _).mpr he3m, (residue_eq_zero_iff _).mpr he6m,
      zero_mul, add_zero] using hr
  have hym := (residue_eq_zero_iff _).mp
    ((pow_eq_zero_iff (by decide : 2 ≠ 0)).mp hy)
  obtain ⟨b, hb⟩ := exists_node_coordinate_factor hgen 1 (by simpa using hym)
  simp only [pow_one] at hb
  have he : π ^ (k + 2) * v.y = π ^ (k + 3) * b := by rw [hb, pow_succ]; ring
  have hn : (W.map (algebraMap A K)).toAffine.Nonsingular
      ((π ^ (k + 2) * v.x : A) : K) ((π ^ (k + 3) * b : A) : K) := by
    simpa only [he] using v.nonsingular
  refine ⟨⟨v.x, b, hn, v.represents.trans ?_⟩⟩
  apply congrArg Affine.Point.toProjective
  simp only [Affine.Point.some.injEq]
  exact ⟨True.intro, congrArg Subtype.val he⟩

end FLT.Mazur
