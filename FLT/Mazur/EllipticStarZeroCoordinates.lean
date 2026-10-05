/-
Copyright (c) 2026 krandder. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: krandder
-/
module

public import FLT.Mazur.EllipticStarZeroResidue
public import FLT.Mazur.EllipticStarZeroSlope

/-!
# Actual point coordinates in the I₀* chart

Singularly reducing points have coordinates (πx,π²y). Points over the same
simple root of the residual cubic have the same component class, and the
component of each such point is killed by two.
-/

@[expose] public section

namespace FLT.Mazur

open WeierstrassCurve IsLocalRing

variable {K : Type*} [Field K] (A : ValuationSubring K) (W : WeierstrassCurve A)

/-- An actual affine representative in the I₀* chart. -/
structure StarZeroCoordinates (π : A) (P : (W.map (algebraMap A K)).toProjective.Point) where
  /-- The x-coordinate divided by π. -/
  x : A
  /-- The y-coordinate divided by π². -/
  y : A
  nonsingular : (W.map (algebraMap A K)).toAffine.Nonsingular
    ((π * x : A) : K) ((π ^ 2 * y : A) : K)
  represents : P = Affine.Point.toProjective (.some _ _ nonsingular)

/-- Every point outside E₀ admits an actual I₀* coordinate witness. -/
theorem exists_starZeroCoordinates {π : A} (hπ : π ≠ 0)
    (hgen : maximalIdeal A = Ideal.span {π}) (e3 e4 e6 : A)
    (h1 : W.a₁ ∈ maximalIdeal A) (h2 : W.a₂ ∈ maximalIdeal A)
    (h3 : W.a₃ = π ^ 2 * e3) (h4 : W.a₄ = π ^ 2 * e4) (h6 : W.a₆ = π ^ 3 * e6)
    (P : (W.map (algebraMap A K)).toProjective.Point) (hP : ¬ SmoothReduction A W P) :
    Nonempty (StarZeroCoordinates A W π P) := by
  have hπm : π ∈ maximalIdeal A := hgen ▸ Ideal.mem_span_singleton_self π
  have hm (n : ℕ) (hn : n ≠ 0) (a : A) : π ^ n * a ∈ maximalIdeal A :=
    (maximalIdeal A).mul_mem_right _ (Ideal.pow_le_self hn (Ideal.pow_mem_pow hπm n))
  obtain ⟨v⟩ := exists_typeIVCoordinates A W π hgen (h3 ▸ hm 2 (by decide) _)
    (h4 ▸ hm 2 (by decide) _) (h6 ▸ hm 3 (by decide) _) P hP
  have hym := starZero_divided_y_mem W hπ hπm v.x v.y e3 e4 e6 h1 h2 h3 h4 h6 v.equation
  obtain ⟨b, hb⟩ := exists_node_coordinate_factor hgen 1 (by simpa using hym)
  simp only [pow_one] at hb
  have he : π * v.y = π ^ 2 * b := by rw [hb]; ring
  have hn : (W.map (algebraMap A K)).toAffine.Nonsingular
      ((π * v.x : A) : K) ((π ^ 2 * b : A) : K) := by simpa only [he] using v.nonsingular
  refine ⟨⟨v.x, b, hn, v.represents.trans ?_⟩⟩
  apply congrArg Affine.Point.toProjective
  simp only [Affine.Point.some.injEq]
  exact ⟨True.intro, congrArg Subtype.val he⟩

variable {A W} {π : A} {P Q : (W.map (algebraMap A K)).toProjective.Point}

/-- The integral representative satisfies the original equation. -/
theorem StarZeroCoordinates.equation (v : StarZeroCoordinates A W π P) :
    W.toAffine.Equation (π * v.x) (π ^ 2 * v.y) :=
  (W.toAffine.map_equation (IsFractionRing.injective A K) _ _).mp v.nonsingular.1

/-- Witnesses over the same simple cubic root have smooth sum. -/
theorem StarZeroCoordinates.smooth_add_of_same
    (v : StarZeroCoordinates A W π P) (w : StarZeroCoordinates A W π Q)
    (hπ : π ≠ 0) (hπm : π ∈ maximalIdeal A) (e1 e2 e3 e4 : A)
    (h1 : W.a₁ = π * e1) (h2 : W.a₂ = π * e2)
    (h3 : W.a₃ = π ^ 2 * e3) (h4 : W.a₄ = π ^ 2 * e4)
    (h6 : W.a₆ ∈ maximalIdeal A) (hx : residue A v.x = residue A w.x)
    (hd : 3 * residue A v.x ^ 2 + 2 * residue A e2 * residue A v.x + residue A e4 ≠ 0) :
    SmoothReduction A W (P + Q) := by
  classical
  have hs := smoothReduction_add_of_starZero_same A W hπ hπm v.x v.y w.x w.y
    e1 e2 e3 e4 h1 h2 h3 h4 h6 v.nonsingular w.nonsingular hx hd
  rw [toProjective_add] at hs
  simpa only [v.represents, w.represents] using hs

/-- Points over the same simple cubic root represent the same actual component. -/
theorem StarZeroCoordinates.component_eq_of_same
    (v : StarZeroCoordinates A W π P) (w : StarZeroCoordinates A W π Q)
    (hπ : π ≠ 0) (hπm : π ∈ maximalIdeal A) (e1 e2 e3 e4 : A)
    (h1 : W.a₁ = π * e1) (h2 : W.a₂ = π * e2)
    (h3 : W.a₃ = π ^ 2 * e3) (h4 : W.a₄ = π ^ 2 * e4)
    (h6 : W.a₆ ∈ maximalIdeal A) (hx : residue A v.x = residue A w.x)
    (hd : 3 * residue A v.x ^ 2 + 2 * residue A e2 * residue A v.x + residue A e4 ≠ 0) :
    ellipticComponentHom A W P = ellipticComponentHom A W Q := by
  have hs : ellipticComponentHom A W P + ellipticComponentHom A W Q = 0 := by
    rw [← map_add, ellipticComponentHom_eq_zero]
    exact v.smooth_add_of_same w hπ hπm e1 e2 e3 e4 h1 h2 h3 h4 h6 hx hd
  have ht : ellipticComponentHom A W P + ellipticComponentHom A W P = 0 := by
    rw [← map_add, ellipticComponentHom_eq_zero]
    exact v.smooth_add_of_same v hπ hπm e1 e2 e3 e4 h1 h2 h3 h4 h6 rfl hd
  exact (add_left_cancel (hs.trans ht.symm)).symm

end FLT.Mazur
