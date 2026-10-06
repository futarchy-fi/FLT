/-
Copyright (c) 2026 krandder. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: krandder
-/
module

public import FLT.EllipticCurve.CubicChord
public import Mathlib.AlgebraicGeometry.EllipticCurve.Projective.Point

/-! # Polynomial projective addition over arbitrary coefficient rings

Polarization proves that the existing projective addition formulas preserve the
cubic equation over every commutative ring, including nonreduced rings. -/

@[expose] public noncomputable section
open AlgebraicGeometry CategoryTheory CategoryTheory.Limits MvPolynomial
set_option backward.isDefEq.respectTransparency false

namespace WeierstrassCurve.CubicCharts
universe u
variable {R : Type u} [CommRing R] (W : WeierstrassCurve R)

/-- The homogeneous Weierstrass cubic evaluated at three coordinates. -/
def cubicForm (P : Fin 3 → R) : R :=
  P 1 ^ 2 * P 2 + W.a₁ * P 0 * P 1 * P 2 + W.a₃ * P 1 * P 2 ^ 2 -
    (P 0 ^ 3 + W.a₂ * P 0 ^ 2 * P 2 + W.a₄ * P 0 * P 2 ^ 2 + W.a₆ * P 2 ^ 3)

/-- Coefficient of s²t in the cubic evaluated on sP+tQ. -/
def cubicPolar (P Q : Fin 3 → R) : R :=
  P 1 ^ 2 * Q 2 + 2 * P 1 * Q 1 * P 2 +
    W.a₁ * (P 0 * P 1 * Q 2 + P 0 * Q 1 * P 2 + Q 0 * P 1 * P 2) +
    W.a₃ * (2 * P 1 * P 2 * Q 2 + Q 1 * P 2 ^ 2) -
    (3 * P 0 ^ 2 * Q 0 + W.a₂ * (P 0 ^ 2 * Q 2 + 2 * P 0 * Q 0 * P 2) +
      W.a₄ * (2 * P 0 * P 2 * Q 2 + Q 0 * P 2 ^ 2) + 3 * W.a₆ * P 2 ^ 2 * Q 2)

theorem cubicForm_linear (P Q : Fin 3 → R) (s t : R) :
    cubicForm W (fun i ↦ s * P i + t * Q i) =
      s ^ 3 * cubicForm W P + s ^ 2 * t * cubicPolar W P Q +
        s * t ^ 2 * cubicPolar W Q P + t ^ 3 * cubicForm W Q := by
  unfold cubicForm cubicPolar
  ring

theorem equation_iff_cubicForm (P : Fin 3 → R) :
    W.toProjective.Equation P ↔ cubicForm W P = 0 := by
  rw [Projective.equation_iff]
  rfl

/-- The third intersection of a chord with the cubic, before negation.
The formula may be zero; its nonvanishing is a separate domain condition. -/
theorem cubicPolar_intersection {P Q : Fin 3 → R}
    (hP : W.toProjective.Equation P) (hQ : W.toProjective.Equation Q) :
    W.toProjective.Equation
      (fun i ↦ cubicPolar W P Q * Q i - cubicPolar W Q P * P i) := by
  rw [equation_iff_cubicForm] at hP hQ ⊢
  have h := cubicForm_linear W Q P (cubicPolar W P Q) (-cubicPolar W Q P)
  simp only [hP, hQ, mul_zero, zero_add, add_zero] at h
  simp only [sub_eq_add_neg, neg_mul] at h ⊢
  rw [h]
  ring

theorem projective_neg_equation {P : Fin 3 → R} (hP : W.toProjective.Equation P) :
    W.toProjective.Equation (W.toProjective.neg P) := by
  rw [Projective.equation_iff] at hP ⊢
  simp only [Projective.neg, Projective.negY, Projective.fin3_def_ext]
  linear_combination hP

theorem projective_addXYZ_polar (P Q : Fin 3 → R) :
    W.toProjective.addXYZ P Q =
      W.toProjective.neg
        (fun i ↦ cubicPolar W P Q * Q i - cubicPolar W Q P * P i) := by
  ext i
  fin_cases i <;>
    simp only [Projective.addXYZ, Projective.addX, Projective.addY,
      Projective.negAddY, Projective.addZ, Projective.neg, Projective.negY,
      Projective.fin3_def_ext, cubicPolar] <;> dsimp <;> ring

/-- The polynomial secant formula preserves the cubic over arbitrary rings.
No reducedness or invertibility of either input's Z-coordinate is required. -/
theorem projective_addXYZ_equation {P Q : Fin 3 → R}
    (hP : W.toProjective.Equation P) (hQ : W.toProjective.Equation Q) :
    W.toProjective.Equation (W.toProjective.addXYZ P Q) := by
  rw [projective_addXYZ_polar]
  exact projective_neg_equation W (cubicPolar_intersection W hP hQ)

/-- At infinity plus an ordinary affine point the projective formula is already normalized. -/
theorem projective_addXYZ_zero_left (x y : R) :
    W.toProjective.addXYZ ![0, 1, 0] ![x, y, 1] = ![x, y, 1] := by
  ext i
  fin_cases i <;>
    simp [Projective.addXYZ, Projective.addX, Projective.addY,
      Projective.negAddY, Projective.addZ, Projective.negY, Projective.fin3_def_ext]
  ring

/-- Projective normalization into the ordinary affine chart. -/
theorem affine_normalize {x y z t : R} (h : W.toProjective.Equation ![x, y, z])
    (ht : z * t = 1) : W.toAffine.Equation (x * t) (y * t) := by
  have hu : IsUnit t := isUnit_iff_exists_inv.mpr ⟨z, by rw [mul_comm, ht]⟩
  have hs := (Projective.equation_smul (W' := W.toProjective) ![x, y, z] hu).mpr h
  have hz : t * z = 1 := by rw [mul_comm, ht]
  rw [Projective.equation_iff] at hs
  rw [Affine.equation_iff']
  simpa [hz, mul_comm] using hs

/-- Affine normalization after extension of coefficients. -/
theorem affine_normalize_algHom {S T : Type*} [CommRing S] [CommRing T]
    [Algebra R S] [Algebra R T] (f : S →ₐ[R] T) {x y z : S} {t : T}
    (h : (W.map (algebraMap R S)).toProjective.Equation ![x, y, z])
    (ht : f z * t = 1) :
    aeval ![f x * t, f y * t] (equation W false) = 0 := by
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
  have hn := affine_normalize (W.map (algebraMap R T)) hp ht
  simpa [Affine.equation_iff', equation, WeierstrassCurve.map] using hn

/-- Projective coordinates of a point in either of the two affine charts. -/
def chartPointCoords {S : Type*} [CommRing S] [Algebra R S] (b : Bool)
    (f : Ring W b →ₐ[R] S) : Fin 3 → S :=
  if b then ![f (coord W b 0), 1, f (coord W b 1)]
  else ![f (coord W b 0), f (coord W b 1), 1]

theorem chartPointCoords_equation {S : Type*} [CommRing S] [Algebra R S] (b : Bool)
    (f : Ring W b →ₐ[R] S) :
    (W.map (algebraMap R S)).toProjective.Equation (chartPointCoords W b f) := by
  have h := eval₂_coord_equation W (S := S) b f.toRingHom
  rw [Projective.equation_iff]
  cases b <;>
    simpa [chartPointCoords, equation, InfinityChart.equation, WeierstrassCurve.map,
      AlgHom.comp_algebraMap] using h

end WeierstrassCurve.CubicCharts
