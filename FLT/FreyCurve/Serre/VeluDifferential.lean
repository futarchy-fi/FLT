/-
Copyright (c) 2026 krandder. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: krandder
-/
module

public import FLT.FreyCurve.Serre.VeluRational
public import Mathlib.FieldTheory.RatFunc.AsPolynomial
public import Mathlib.Algebra.Polynomial.Derivative
public import Mathlib.RingTheory.Derivation.Basic

/-!
# Integrating the differential identity for Vélu sums

The formal derivative on rational functions is defined by the quotient rule and
proved to be independent of a fraction presentation. In characteristic zero its
kernel consists exactly of constants. Applying this derivation to the rational
Vélu sums shows that the curve equation has a constant residual.

The value of this constant, nonsingularity, and additivity remain to be proved.
-/

@[expose] public section

open scoped Polynomial
namespace RatFunc
variable {K : Type*} [Field K]

/-- The formal derivative of a rational function, computed from its reduced fraction. -/
noncomputable def formalDeriv (f : K⟮X⟯) : K⟮X⟯ :=
  algebraMap K[X] K⟮X⟯ (f.num.derivative * f.denom - f.num * f.denom.derivative) /
    (algebraMap K[X] K⟮X⟯ f.denom) ^ 2

/-- In characteristic zero, the kernel of the formal derivative consists of constants. -/
theorem formalDeriv_eq_zero_iff [CharZero K] (f : K⟮X⟯) :
    formalDeriv f = 0 ↔ ∃ c : K, f = RatFunc.C c := by
  constructor
  · intro h
    have hw : f.num.derivative * f.denom = f.num * f.denom.derivative := by
      have hn : algebraMap K[X] K⟮X⟯ f.denom ≠ 0 := algebraMap_ne_zero f.denom_ne_zero
      have hz := (div_eq_zero_iff).mp h
      have hh : algebraMap K[X] K⟮X⟯
          (f.num.derivative * f.denom - f.num * f.denom.derivative) = 0 := by
        rcases hz with hz | hz
        · exact hz
        · exact (pow_ne_zero 2 hn hz).elim
      exact sub_eq_zero.mp ((algebraMap_injective K) (hh.trans (map_zero _).symm))
    have hqd : f.denom ∣ f.denom.derivative :=
      f.isCoprime_num_denom.symm.dvd_of_dvd_mul_left (hw ▸ dvd_mul_left _ _)
    have hq := Polynomial.dvd_derivative_iff.mp hqd
    have hp : f.num.derivative = 0 := by
      rw [hq, mul_zero] at hw
      exact (mul_eq_zero.mp hw).resolve_right f.denom_ne_zero
    refine ⟨f.num.coeff 0 / f.denom.coeff 0, ?_⟩
    calc
      f = algebraMap K[X] K⟮X⟯ f.num / algebraMap K[X] K⟮X⟯ f.denom :=
        f.num_div_denom.symm
      _ = RatFunc.C (f.num.coeff 0 / f.denom.coeff 0) := by
        conv_lhs =>
          rw [Polynomial.eq_C_of_derivative_eq_zero hp,
            Polynomial.eq_C_of_derivative_eq_zero hq]
        rw [algebraMap_C, algebraMap_C, map_div₀]
  · rintro ⟨c, rfl⟩
    simp [formalDeriv]

/-- The quotient rule agrees with any presentation with nonzero denominator. -/
theorem formalDeriv_of_div (f : K⟮X⟯) (p q : K[X]) (hq : q ≠ 0)
    (hf : f = algebraMap K[X] K⟮X⟯ p / algebraMap K[X] K⟮X⟯ q) :
    formalDeriv f =
      algebraMap K[X] K⟮X⟯ (p.derivative * q - p * q.derivative) /
        (algebraMap K[X] K⟮X⟯ q) ^ 2 := by
  have hc : f.num * q = p * f.denom := (num_mul_eq_mul_denom_iff hq).mpr hf
  have hd := congrArg Polynomial.derivative hc
  simp only [Polynomial.derivative_mul] at hd
  have hpoly :
      (f.num.derivative * f.denom - f.num * f.denom.derivative) * q ^ 2 =
        (p.derivative * q - p * q.derivative) * f.denom ^ 2 := by
    linear_combination f.denom * q * hd -
      (f.denom.derivative * q + f.denom * q.derivative) * hc
  have hn : algebraMap K[X] K⟮X⟯ f.denom ≠ 0 := algebraMap_ne_zero f.denom_ne_zero
  have hq' : algebraMap K[X] K⟮X⟯ q ≠ 0 := algebraMap_ne_zero hq
  apply (div_eq_div_iff (pow_ne_zero 2 hn) (pow_ne_zero 2 hq')).mpr
  simpa only [map_mul, map_pow] using congrArg (algebraMap K[X] K⟮X⟯) hpoly

/-- The formal derivative preserves addition. -/
theorem formalDeriv_add (f g : K⟮X⟯) :
    formalDeriv (f + g) = formalDeriv f + formalDeriv g := by
  have hn := algebraMap_ne_zero (K := K) f.denom_ne_zero
  have hm := algebraMap_ne_zero (K := K) g.denom_ne_zero
  have hrepr : f + g =
      algebraMap K[X] K⟮X⟯ (f.num * g.denom + g.num * f.denom) /
        algebraMap K[X] K⟮X⟯ (f.denom * g.denom) := by
    conv_lhs => rw [← f.num_div_denom, ← g.num_div_denom]
    simp only [map_add, map_mul]
    field_simp
  rw [formalDeriv_of_div _ _ _ (mul_ne_zero f.denom_ne_zero g.denom_ne_zero) hrepr]
  simp only [formalDeriv, Polynomial.derivative_mul,
    map_add, map_sub, map_mul]
  field_simp
  ring

/-- The formal derivative satisfies the product rule. -/
theorem formalDeriv_mul (f g : K⟮X⟯) :
    formalDeriv (f * g) = f * formalDeriv g + g * formalDeriv f := by
  have hn := algebraMap_ne_zero (K := K) f.denom_ne_zero
  have hm := algebraMap_ne_zero (K := K) g.denom_ne_zero
  have hrepr : f * g = algebraMap K[X] K⟮X⟯ (f.num * g.num) /
      algebraMap K[X] K⟮X⟯ (f.denom * g.denom) := by
    conv_lhs => rw [← f.num_div_denom, ← g.num_div_denom]
    simp only [map_mul, div_mul_div_comm]
  rw [formalDeriv_of_div _ _ _ (mul_ne_zero f.denom_ne_zero g.denom_ne_zero) hrepr]
  conv_rhs =>
    lhs
    lhs
    rw [← f.num_div_denom]
  conv_rhs =>
    rhs
    lhs
    rw [← g.num_div_denom]
  simp only [formalDeriv, Polynomial.derivative_mul, map_add, map_sub, map_mul]
  field_simp
  ring

/-- The formal derivative extends the polynomial derivative. -/
theorem formalDeriv_polynomial (p : K[X]) :
    formalDeriv (algebraMap K[X] K⟮X⟯ p) = algebraMap K[X] K⟮X⟯ p.derivative := by
  rw [formalDeriv_of_div _ p 1 one_ne_zero (by simp)]
  simp

/-- Constants have zero formal derivative. -/
@[simp] theorem formalDeriv_C (c : K) : formalDeriv (RatFunc.C c) = 0 := by
  rw [← algebraMap_C, formalDeriv_polynomial]
  simp

/-- The formal derivative of the indeterminate is one. -/
@[simp] theorem formalDeriv_X : formalDeriv (RatFunc.X : K⟮X⟯) = 1 := by
  rw [← algebraMap_X, formalDeriv_polynomial]
  simp

/-- The formal derivative as a derivation over the coefficient field. -/
noncomputable def formalDerivation : Derivation K K⟮X⟯ K⟮X⟯ where
  toFun := formalDeriv
  map_add' := formalDeriv_add
  map_smul' c f := by
    simp only [Algebra.smul_def, algebraMap_eq_C, RingHom.id_apply,
      formalDeriv_mul, formalDeriv_C, mul_zero, add_zero]
  map_one_eq_zero' := by
    change formalDeriv (1 : K⟮X⟯) = 0
    simpa only [map_one] using formalDeriv_C (1 : K)
  leibniz' f g := by
    change formalDeriv (f * g) = f * formalDeriv g + g * formalDeriv f
    exact formalDeriv_mul f g

/-- The derivation computes the quotient-rule derivative. -/
theorem formalDerivation_apply (f : K⟮X⟯) :
    formalDerivation f = formalDeriv f := rfl

/-- The derivation vanishes on constants. -/
@[simp] theorem formalDerivation_C (c : K) : formalDerivation (C c) = 0 :=
  formalDeriv_C c

/-- The derivation sends the indeterminate to one. -/
@[simp] theorem formalDerivation_X : formalDerivation (X : K⟮X⟯) = 1 :=
  formalDeriv_X

/-- The indeterminate is distinct from every constant. -/
theorem X_sub_C_ne_zero (c : K) : (RatFunc.X : K⟮X⟯) - RatFunc.C c ≠ 0 := by
  simpa only [map_sub, algebraMap_X, algebraMap_C] using
    algebraMap_ne_zero (Polynomial.X_sub_C_ne_zero c)

open WeierstrassCurve.Velu

/-- Differentiating one pole contribution gives its slope expression. -/
theorem formalDerivation_polePart (a c u : K) :
    formalDerivation (polePart (C a) (C c) (C u) X) =
      poleSlope (C a) (C c) (C u) X := by
  simp [polePart, Derivation.leibniz_div, Derivation.leibniz_pow, smul_eq_mul]
  dsimp [poleSlope]
  have hn := X_sub_C_ne_zero u
  field_simp
  ring

/-- Differentiating the slope expression gives its curvature expression. -/
theorem formalDerivation_poleSlope (a c u : K) :
    formalDerivation (poleSlope (C a) (C c) (C u) X) =
      poleCurvature (C a) (C c) (C u) X := by
  have htwo : formalDerivation (2 : K⟮X⟯) = 0 :=
    Derivation.map_natCast formalDerivation 2
  simp [poleSlope, Derivation.leibniz_div, Derivation.leibniz_pow, smul_eq_mul, htwo]
  dsimp [poleCurvature]
  have hn := X_sub_C_ne_zero u
  field_simp
  ring

end RatFunc

namespace WeierstrassCurve.Velu
open scoped BigOperators
open RatFunc
variable {K : Type*} [Field K] [DecidableEq K]

/-- The rational x-coordinate sum over distinct kernel abscissae. -/
noncomputable def xFunction (E : WeierstrassCurve K)
    (G : AddSubgroup E.toAffine.Point) [Fintype G] : K⟮X⟯ :=
  X + ∑ u ∈ kernelAbscissae E G,
    polePart (C (4 * u ^ 3 + E.b₂ * u ^ 2 + 2 * E.b₄ * u + E.b₆))
      (C (6 * u ^ 2 + E.b₂ * u + E.b₄)) (C u) X

/-- The first derivative expression of the rational x-coordinate. -/
noncomputable def slopeFunction (E : WeierstrassCurve K)
    (G : AddSubgroup E.toAffine.Point) [Fintype G] : K⟮X⟯ :=
  1 + ∑ u ∈ kernelAbscissae E G,
    poleSlope (C (4 * u ^ 3 + E.b₂ * u ^ 2 + 2 * E.b₄ * u + E.b₆))
      (C (6 * u ^ 2 + E.b₂ * u + E.b₄)) (C u) X

/-- The second derivative expression of the rational x-coordinate. -/
noncomputable def curvatureFunction (E : WeierstrassCurve K)
    (G : AddSubgroup E.toAffine.Point) [Fintype G] : K⟮X⟯ :=
  ∑ u ∈ kernelAbscissae E G,
    poleCurvature (C (4 * u ^ 3 + E.b₂ * u ^ 2 + 2 * E.b₄ * u + E.b₆))
      (C (6 * u ^ 2 + E.b₂ * u + E.b₄)) (C u) X

/-- The slope expression is the derivative of the rational x-coordinate. -/
theorem derivation_xFunction (E : WeierstrassCurve K)
    (G : AddSubgroup E.toAffine.Point) [Fintype G] :
    formalDerivation (xFunction E G) = slopeFunction E G := by
  rw [xFunction, map_add, formalDerivation_X, slopeFunction]
  congr 1
  rw [map_sum]
  apply Finset.sum_congr rfl
  intro u _
  exact formalDerivation_polePart _ _ _

/-- The curvature expression is the derivative of the slope expression. -/
theorem derivation_slopeFunction (E : WeierstrassCurve K)
    (G : AddSubgroup E.toAffine.Point) [Fintype G] :
    formalDerivation (slopeFunction E G) = curvatureFunction E G := by
  rw [slopeFunction, map_add, Derivation.map_one_eq_zero, zero_add,
    curvatureFunction, map_sum]
  apply Finset.sum_congr rfl
  intro u _
  exact formalDerivation_poleSlope _ _ _

/-- The kernel differential identity holds in the rational function field. -/
theorem rational_differential_eq_zero [NeZero (2 : K)] (E : WeierstrassCurve K)
    (G : AddSubgroup E.toAffine.Point) [Fintype G]
    (hodd : ∀ Q : G, Q ≠ 0 → Q ≠ -Q) :
    2 * (4 * X ^ 3 + C E.b₂ * X ^ 2 + 2 * C E.b₄ * X + C E.b₆) *
        curvatureFunction E G +
      2 * (6 * X ^ 2 + C E.b₂ * X + C E.b₄) * slopeFunction E G -
      12 * xFunction E G ^ 2 - 2 * C E.b₂ * xFunction E G - 2 * C E.b₄ +
      20 * C (∑ u ∈ kernelAbscissae E G, (6 * u ^ 2 + E.b₂ * u + E.b₄)) = 0 := by
  classical
  let S := kernelAbscissae E G
  have hinj := (RatFunc.C : K →+* K⟮X⟯).injective
  have hx : ∀ u ∈ S.image (RatFunc.C : K → K⟮X⟯), (X : K⟮X⟯) ≠ u := by
    intro u hu
    obtain ⟨v, _, rfl⟩ := Finset.mem_image.mp hu
    exact sub_ne_zero.mp (X_sub_C_ne_zero v)
  have h0 (u : K) (hu : u ∈ S) := congrArg (RatFunc.C : K → K⟮X⟯)
    (kernel_pole_relations E G hodd hu).1
  have h1 (u : K) (hu : u ∈ S) := congrArg (RatFunc.C : K → K⟮X⟯)
    (kernel_pole_relations E G hodd hu).2
  have h := sum_polePart_differential_eq_zero (S.image (RatFunc.C : K → K⟮X⟯))
    (C E.b₂) (C E.b₄) (C E.b₆) X hx
  have hh := h (by
    intro u hu
    obtain ⟨v, hv, rfl⟩ := Finset.mem_image.mp hu
    rw [← Finset.image_erase hinj]
    simpa only [Finset.sum_image (fun _ _ _ _ h => hinj h),
      polePart, map_add, map_sub, map_mul, map_pow, map_ofNat, map_div₀, map_sum]
      using h0 v hv) (by
    intro u hu
    obtain ⟨v, hv, rfl⟩ := Finset.mem_image.mp hu
    rw [← Finset.image_erase hinj]
    simpa only [Finset.sum_image (fun _ _ _ _ h => hinj h),
      polePart, poleSlope, map_add, map_sub, map_mul, map_pow,
      map_ofNat, map_div₀, map_neg, map_sum, map_zero] using h1 v hv)
  simpa only [xFunction, slopeFunction, curvatureFunction, S,
    Finset.sum_image (fun _ _ _ _ h => hinj h), map_add, map_mul, map_pow,
    map_ofNat, map_sum] using hh

/-- The rational equation has a constant residual in characteristic zero. -/
theorem rational_equation_up_to_constant [CharZero K] (E : WeierstrassCurve K)
    (G : AddSubgroup E.toAffine.Point) [Fintype G]
    (hodd : ∀ Q : G, Q ≠ 0 → Q ≠ -Q) :
    ∃ k : K,
      (4 * X ^ 3 + C E.b₂ * X ^ 2 + 2 * C E.b₄ * X + C E.b₆) *
          slopeFunction E G ^ 2 =
        4 * xFunction E G ^ 3 + C E.b₂ * xFunction E G ^ 2 +
          (2 * C E.b₄ - 20 * C (∑ u ∈ kernelAbscissae E G,
            (6 * u ^ 2 + E.b₂ * u + E.b₄))) * xFunction E G + C k := by
  let R : K⟮X⟯ :=
    (C 4 * X ^ 3 + C E.b₂ * X ^ 2 + C 2 * C E.b₄ * X + C E.b₆) *
        slopeFunction E G ^ 2 -
      C 4 * xFunction E G ^ 3 - C E.b₂ * xFunction E G ^ 2 -
      (C 2 * C E.b₄ - C 20 * C (∑ u ∈ kernelAbscissae E G,
        (6 * u ^ 2 + E.b₂ * u + E.b₄))) * xFunction E G
  have hd : formalDerivation R = 0 := by
    dsimp only [R]
    simp only [map_add, map_sub, Derivation.leibniz, Derivation.leibniz_pow,
      formalDerivation_C, formalDerivation_X, derivation_xFunction, derivation_slopeFunction,
      smul_eq_mul, nsmul_eq_mul, Nat.cast_ofNat, Nat.reduceSub,
      pow_one, mul_one, mul_zero, add_zero, sub_zero]
    simp only [map_ofNat]
    linear_combination slopeFunction E G * rational_differential_eq_zero E G hodd
  obtain ⟨k, hk⟩ := (formalDeriv_eq_zero_iff R).mp hd
  refine ⟨k, ?_⟩
  dsimp only [R] at hk
  simp only [map_ofNat] at hk
  linear_combination hk

end WeierstrassCurve.Velu
