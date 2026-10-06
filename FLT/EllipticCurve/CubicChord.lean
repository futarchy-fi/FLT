/-
Copyright (c) 2026 krandder. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: krandder
-/
module

public import FLT.EllipticCurve.CubicTangent

/-! # Homogeneous chord formulas

Polynomial certificates for addition with a possibly vertical chord. The
coordinates define morphisms only on opens where a target coordinate is a unit. -/

@[expose] public noncomputable section
open AlgebraicGeometry CategoryTheory CategoryTheory.Limits MvPolynomial
set_option backward.isDefEq.respectTransparency false

namespace WeierstrassCurve.CubicCharts
universe u
variable {R : Type u} [CommRing R] (W : WeierstrassCurve R)

/-- Numerator of the affine x-coordinate for a slope s/t. -/
def chordXNumerator (x₁ x₂ s t : R) : R :=
  s ^ 2 + W.a₁ * s * t - (W.a₂ + x₁ + x₂) * t ^ 2

/-- Homogeneous x-coordinate of the chord sum. -/
def chordX (x₁ x₂ s t : R) : R := chordXNumerator W x₁ x₂ s t * t

/-- Homogeneous y-coordinate of the chord sum. -/
def chordY (x₁ x₂ y₁ s t : R) : R :=
  -s * (chordXNumerator W x₁ x₂ s t - x₁ * t ^ 2) -
    (y₁ + W.a₃) * t ^ 3 - W.a₁ * chordXNumerator W x₁ x₂ s t * t

/-- The remaining coefficient in the intersection of the line and the cubic. -/
def chordObstruction (x₁ x₂ y₁ s t : R) : R :=
  s ^ 2 * (x₂ - x₁) + s * t * (W.a₁ * x₂ + 2 * y₁ + W.a₃) -
    t ^ 2 * chordNumerator W x₁ x₂ y₁

/-- The polynomial chord formula lies on the projective cubic when the residual coefficient
vanishes. This identity does not require either chord coordinate to be invertible. -/
theorem chord_projective_equation {x₁ y₁ x₂ s t : R}
    (h₁ : W.toAffine.Equation x₁ y₁) (hk : chordObstruction W x₁ x₂ y₁ s t = 0) :
    W.toProjective.Equation ![chordX W x₁ x₂ s t, chordY W x₁ x₂ y₁ s t, t ^ 3] := by
  rw [Affine.equation_iff'] at h₁
  rw [Projective.equation_iff]
  simp only [Projective.fin3_def_ext]
  unfold chordObstruction chordNumerator at hk
  unfold chordX chordY chordXNumerator
  linear_combination t ^ 9 * h₁ +
    t ^ 5 * (s ^ 2 + W.a₁ * s * t - (W.a₂ + x₁ + x₂) * t ^ 2 - x₁ * t ^ 2) * hk

theorem secant_chord_obstruction {x₁ y₁ x₂ y₂ : R}
    (h₁ : W.toAffine.Equation x₁ y₁) (h₂ : W.toAffine.Equation x₂ y₂) :
    chordObstruction W x₁ x₂ y₁ (y₂ - y₁) (x₂ - x₁) = 0 := by
  have h := chord_relation W h₁ h₂
  unfold chordObstruction chordDenominator at *
  linear_combination (x₂ - x₁) * h

theorem tangent_chord_obstruction {x₁ y₁ x₂ y₂ : R}
    (h₁ : W.toAffine.Equation x₁ y₁) (h₂ : W.toAffine.Equation x₂ y₂) :
    chordObstruction W x₁ x₂ y₁ (chordNumerator W x₁ x₂ y₁)
      (chordDenominator W x₂ y₁ y₂) = 0 := by
  have h := chord_relation W h₁ h₂
  unfold chordObstruction chordDenominator at *
  linear_combination -chordNumerator W x₁ x₂ y₁ * h

/-- At a vertical chord the output is infinity, provided its y-coordinate is invertible. -/
@[simp] theorem chordX_vertical (x₁ x₂ s : R) : chordX W x₁ x₂ s 0 = 0 := by
  simp [chordX]

@[simp] theorem chordY_vertical (x₁ x₂ y₁ s : R) :
    chordY W x₁ x₂ y₁ s 0 = -s ^ 3 := by
  simp [chordY, chordXNumerator]
  ring

/-- Normalize a projective cubic point in the infinity chart, using an explicit inverse. -/
theorem infinity_normalize {x y z t : R} (h : W.toProjective.Equation ![x, y, z])
    (ht : y * t = 1) :
    eval ![x * t, z * t] (equation W true) = 0 := by
  have hu : IsUnit t := isUnit_iff_exists_inv.mpr ⟨y, by rw [mul_comm, ht]⟩
  have hs := (Projective.equation_smul (W' := W.toProjective) ![x, y, z] hu).mpr h
  rw [Projective.equation_iff] at hs
  have hy : t * y = 1 := by rw [mul_comm, ht]
  simpa [equation, InfinityChart.equation, hy, mul_comm] using hs

/-- A chart algebra homomorphism gives an algebra-valued point of the affine equation. -/
theorem chart_hom_equation {S : Type*} [CommRing S] [Algebra R S]
    (f : Ring W false →ₐ[R] S) :
    (W.map (algebraMap R S)).toAffine.Equation (f (coord W false 0)) (f (coord W false 1)) := by
  have h := eval₂_coord_equation W (S := S) false f.toRingHom
  simpa [equation, Affine.equation_iff', WeierstrassCurve.map, AlgHom.comp_algebraMap] using h

/-- Normalization after extension of coefficients, stated for algebra homomorphisms. -/
theorem infinity_normalize_algHom {S T : Type*} [CommRing S] [CommRing T]
    [Algebra R S] [Algebra R T] (f : S →ₐ[R] T) {x y z : S} {t : T}
    (h : (W.map (algebraMap R S)).toProjective.Equation ![x, y, z])
    (ht : f y * t = 1) :
    aeval ![f x * t, f z * t] (equation W true) = 0 := by
  have hp := Projective.Equation.map (S := T) f.toRingHom h
  have hb : (W.map (algebraMap R S)).map f.toRingHom = W.map (algebraMap R T) := by
    rw [WeierstrassCurve.map_map]
    exact congrArg W.map f.comp_algebraMap
  change ((W.map (algebraMap R S)).map f.toRingHom).toProjective.Equation _ at hp
  rw [hb] at hp
  have hv : f.toRingHom ∘ ![x, y, z] = ![f x, f y, f z] := by
    ext i
    fin_cases i <;> rfl
  rw [hv] at hp
  have hn := infinity_normalize (W.map (algebraMap R T)) hp ht
  rw [← map_equation W, eval_map] at hn
  exact hn

/-- On the affine target chart the homogeneous x-coordinate agrees with the slope formula. -/
theorem chordX_affine {x₁ x₂ s t v : R} (ht : t * v = 1) :
    chordX W x₁ x₂ s t * v ^ 3 = W.toAffine.addX x₁ x₂ (s * v) := by
  unfold chordX chordXNumerator Affine.addX
  linear_combination
    (s ^ 2 * v ^ 2 + W.a₁ * s * v * (t * v + 1) -
      (W.a₂ + x₁ + x₂) * ((t * v) ^ 2 + t * v + 1)) * ht

/-- Four chord domains cover every pair whose first point is nonsingular.
The last two domains use the infinity chart and include the vertical cases. -/
theorem chord_domains_cover {K : Type*} [Field K] (E : WeierstrassCurve K)
    {x₁ y₁ x₂ y₂ : K} (h : E.toAffine.Nonsingular x₁ y₁) :
    x₂ - x₁ ≠ 0 ∨ chordDenominator E x₂ y₁ y₂ ≠ 0 ∨
      chordY E x₁ x₂ y₁ (y₂ - y₁) (x₂ - x₁) ≠ 0 ∨
      chordY E x₁ x₂ y₁ (chordNumerator E x₁ x₂ y₁)
        (chordDenominator E x₂ y₁ y₂) ≠ 0 := by
  by_cases hx : x₂ = x₁
  · subst x₂
    by_cases hd : chordDenominator E x₁ y₁ y₂ = 0
    · by_cases hy : y₂ = y₁
      · subst y₂
        have hn : chordNumerator E x₁ x₁ y₁ ≠ 0 := by
          intro hz
          rcases ((Affine.nonsingular_iff' _ _).mp h).2 with hx | hy
          · apply hx
            unfold chordNumerator at hz
            linear_combination -hz
          · apply hy
            unfold chordDenominator at hd
            linear_combination hd
        exact Or.inr (Or.inr (Or.inr (by
          rw [hd, chordY_vertical]
          exact neg_ne_zero.mpr (pow_ne_zero 3 hn))))
      · exact Or.inr (Or.inr (Or.inl (by
          rw [sub_self, chordY_vertical]
          exact neg_ne_zero.mpr (pow_ne_zero 3 (sub_ne_zero.mpr hy)))))
    · exact Or.inr (Or.inl hd)
  · exact Or.inl (sub_ne_zero.mpr hx)

end WeierstrassCurve.CubicCharts
