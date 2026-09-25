/-
Copyright (c) 2026 krandder. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: krandder
-/
module

public import FLT.FreyCurve.Serre.VeluTranslation

/-!
# Evaluation at infinity for the quadratic function field

Negative degree bounds characterize vanishing at infinity. They give a unique
value compatible with addition, multiplication, and inversion at nonzero values.
The generic point translated by an affine point has that point as its value
at infinity. Rational substitution preserves these values at regular inputs.
-/

@[expose] public section


namespace RatFunc
variable {K : Type*} [Field K]

/-- The function has the specified finite value at infinity. -/
def HasValueAtInfinity (f : K⟮X⟯) (c : K) : Prop := DegreeLE (f - RatFunc.C c) (-1)

/-- A constant rational function has its own value at infinity. -/
theorem HasValueAtInfinity.C (c : K) : HasValueAtInfinity (RatFunc.C c) c := by
  simp [HasValueAtInfinity, DegreeLE]

/-- The zero rational function has value zero at infinity. -/
theorem HasValueAtInfinity.zero : HasValueAtInfinity (0 : K⟮X⟯) 0 := by
  simpa using HasValueAtInfinity.C (0 : K)

/-- A rational function of negative degree vanishes at infinity. -/
theorem HasValueAtInfinity.of_degreeLE {f : K⟮X⟯} (hf : DegreeLE f (-1)) :
    HasValueAtInfinity f 0 := by simpa [HasValueAtInfinity] using hf

/-- A function has at most one finite value at infinity. -/
theorem HasValueAtInfinity.unique {f : K⟮X⟯} {c d : K}
    (hc : HasValueAtInfinity f c) (hd : HasValueAtInfinity f d) : c = d := by
  apply sub_eq_zero.mp
  apply DegreeLE.const_eq_zero
  convert hd.sub hc using 1
  simp only [map_sub]
  ring

/-- A rational function with finite value at infinity has degree at most zero. -/
theorem HasValueAtInfinity.degreeLE {f : K⟮X⟯} {c : K}
    (hf : HasValueAtInfinity f c) : DegreeLE f 0 := by
  have h := (hf.mono (by omega : (-1 : ℤ) ≤ 0)).add (DegreeLE.C c)
  simpa using h

/-- Evaluation at infinity respects addition. -/
theorem HasValueAtInfinity.add {f g : K⟮X⟯} {c d : K}
    (hf : HasValueAtInfinity f c) (hg : HasValueAtInfinity g d) :
    HasValueAtInfinity (f + g) (c + d) := by
  unfold HasValueAtInfinity at *
  convert hf.add hg using 1
  simp only [map_add]
  ring

/-- Evaluation at infinity respects negation. -/
theorem HasValueAtInfinity.neg {f : K⟮X⟯} {c : K}
    (hf : HasValueAtInfinity f c) : HasValueAtInfinity (-f) (-c) := by
  unfold HasValueAtInfinity at *
  convert hf.neg using 1
  simp only [map_neg]
  ring

/-- Evaluation at infinity respects subtraction. -/
theorem HasValueAtInfinity.sub {f g : K⟮X⟯} {c d : K}
    (hf : HasValueAtInfinity f c) (hg : HasValueAtInfinity g d) :
    HasValueAtInfinity (f - g) (c - d) := by
  simpa only [sub_eq_add_neg] using hf.add hg.neg

/-- Evaluation at infinity respects multiplication. -/
theorem HasValueAtInfinity.mul {f g : K⟮X⟯} {c d : K}
    (hf : HasValueAtInfinity f c) (hg : HasValueAtInfinity g d) :
    HasValueAtInfinity (f * g) (c * d) := by
  have h1 : DegreeLE ((f - RatFunc.C c) * g) (-1) := by simpa using DegreeLE.mul hf hg.degreeLE
  have h2 := hg.const_mul c
  unfold HasValueAtInfinity
  convert h1.add h2 using 1
  simp only [map_mul]
  ring

/-- A nonzero value at infinity implies the rational function is nonzero. -/
theorem HasValueAtInfinity.ne_zero {f : K⟮X⟯} {c : K}
    (hf : HasValueAtInfinity f c) (hc : c ≠ 0) : f ≠ 0 := by
  intro h
  subst f
  exact hc (hf.unique HasValueAtInfinity.zero)

/-- A nonzero finite value at infinity forces degree zero. -/
theorem HasValueAtInfinity.intDegree {f : K⟮X⟯} {c : K}
    (hf : HasValueAtInfinity f c) (hc : c ≠ 0) : f.intDegree = 0 := by
  have hle := hf.degreeLE.resolve_left (hf.ne_zero hc)
  by_contra h
  have hneg : DegreeLE f (-1) := Or.inr (by omega)
  exact hc (hf.unique (HasValueAtInfinity.of_degreeLE hneg))

/-- Evaluation at infinity respects inversion at a nonzero value. -/
theorem HasValueAtInfinity.inv {f : K⟮X⟯} {c : K}
    (hf : HasValueAtInfinity f c) (hc : c ≠ 0) :
    HasValueAtInfinity f⁻¹ c⁻¹ := by
  have hfi : DegreeLE f⁻¹ 0 := Or.inr (by rw [intDegree_inv, hf.intDegree hc]; omega)
  have h : DegreeLE (RatFunc.C c⁻¹ * (-(f - RatFunc.C c) * f⁻¹)) (-1) := by
    simpa using ((show DegreeLE (f - RatFunc.C c) (-1) from hf).neg.mul hfi).const_mul c⁻¹
  unfold HasValueAtInfinity
  convert h using 1
  rw [map_inv₀]
  field_simp [hf.ne_zero hc, (map_ne_zero RatFunc.C).mpr hc]
  ring

/-- Evaluation at infinity respects division by a function with nonzero value. -/
theorem HasValueAtInfinity.div {f g : K⟮X⟯} {c d : K}
    (hf : HasValueAtInfinity f c) (hg : HasValueAtInfinity g d) (hd : d ≠ 0) :
    HasValueAtInfinity (f / g) (c / d) := by
  simpa only [div_eq_mul_inv] using hf.mul (hg.inv hd)

end RatFunc

namespace WeierstrassCurve.Velu
open RatFunc
variable {K : Type*} [Field K] [CharZero K]
variable (E : WeierstrassCurve K)

/-- The function has the specified finite value at infinity. -/
def HasValueAtInfinity (z : FunctionField E) (c : K) : Prop :=
  RatFunc.HasValueAtInfinity z.re c ∧ DegreeLE z.im (-2)

omit [CharZero K] in
/-- A base-field constant retains its value at infinity. -/
theorem HasValueAtInfinity.constant (c : K) :
    HasValueAtInfinity E (algebraMap K _ c) c := by
  constructor
  · simpa using RatFunc.HasValueAtInfinity.C c
  · simp [DegreeLE]

omit [CharZero K] in
/-- Lifting a rational function preserves its value at infinity. -/
theorem HasValueAtInfinity.lift {f : K⟮X⟯} {c : K}
    (hf : RatFunc.HasValueAtInfinity f c) : HasValueAtInfinity E (liftX E f) c := by
  exact ⟨hf, DegreeLE.zero _⟩

variable {E}

omit [CharZero K] in
/-- A function has at most one finite value at infinity. -/
theorem HasValueAtInfinity.unique {z : FunctionField E} {c d : K}
    (hc : HasValueAtInfinity E z c) (hd : HasValueAtInfinity E z d) : c = d :=
  hc.1.unique hd.1

omit [CharZero K] in
/-- Evaluation at infinity respects addition. -/
theorem HasValueAtInfinity.add {z w : FunctionField E} {c d : K}
    (hz : HasValueAtInfinity E z c) (hw : HasValueAtInfinity E w d) :
    HasValueAtInfinity E (z + w) (c + d) := by
  exact ⟨hz.1.add hw.1, hz.2.add hw.2⟩

omit [CharZero K] in
/-- Evaluation at infinity respects negation. -/
theorem HasValueAtInfinity.neg {z : FunctionField E} {c : K}
    (hz : HasValueAtInfinity E z c) : HasValueAtInfinity E (-z) (-c) :=
  ⟨hz.1.neg, hz.2.neg⟩

omit [CharZero K] in
/-- Evaluation at infinity respects subtraction. -/
theorem HasValueAtInfinity.sub {z w : FunctionField E} {c d : K}
    (hz : HasValueAtInfinity E z c) (hw : HasValueAtInfinity E w d) :
    HasValueAtInfinity E (z - w) (c - d) := by
  simpa only [sub_eq_add_neg] using hz.add hw.neg

/-- Evaluation at infinity respects multiplication. -/
theorem HasValueAtInfinity.mul {z w : FunctionField E} {c d : K}
    (hz : HasValueAtInfinity E z c) (hw : HasValueAtInfinity E w d) :
    HasValueAtInfinity E (z * w) (c * d) := by
  have hF : DegreeLE (cubicFunction E) 3 := Or.inr (by rw [intDegree_cubicFunction])
  have hsmall : DegreeLE (cubicFunction E * z.im * w.im) (-1) := by
    simpa using (hF.mul hz.2).mul hw.2
  constructor
  · simpa only [QuadraticAlgebra.re_mul, add_zero] using
      (hz.1.mul hw.1).add (RatFunc.HasValueAtInfinity.of_degreeLE hsmall)
  · simpa only [QuadraticAlgebra.im_mul, zero_mul, add_zero] using
      (show DegreeLE (z.re * w.im + z.im * w.re) (-2) from
        (DegreeLE.add (by simpa using hz.1.degreeLE.mul hw.2)
          (by simpa using hz.2.mul hw.1.degreeLE)))

/-- The quadratic norm has the square of the value at infinity. -/
theorem HasValueAtInfinity.norm {z : FunctionField E} {c : K}
    (hz : HasValueAtInfinity E z c) : RatFunc.HasValueAtInfinity z.norm (c ^ 2) := by
  have hF : DegreeLE (cubicFunction E) 3 := Or.inr (by rw [intDegree_cubicFunction])
  have hsmall : DegreeLE (cubicFunction E * z.im * z.im) (-1) := by
    simpa using (hF.mul hz.2).mul hz.2
  simpa only [QuadraticAlgebra.norm_def, zero_mul, add_zero, sub_zero, pow_two] using
    (hz.1.mul hz.1).sub (RatFunc.HasValueAtInfinity.of_degreeLE hsmall)

/-- Evaluation at infinity respects inversion at a nonzero value. -/
theorem HasValueAtInfinity.inv {z : FunctionField E} {c : K}
    (hz : HasValueAtInfinity E z c) (hc : c ≠ 0) :
    HasValueAtInfinity E z⁻¹ c⁻¹ := by
  have hn := hz.norm.inv (pow_ne_zero 2 hc)
  constructor
  · have h := hn.mul hz.1
    convert h using 1
    · simp [QuadraticAlgebra.inv_def, smul_eq_mul]
    · field_simp
  · simpa [QuadraticAlgebra.inv_def, smul_eq_mul] using hn.degreeLE.mul hz.2.neg

/-- Evaluation at infinity respects division by a function with nonzero value. -/
theorem HasValueAtInfinity.div {z w : FunctionField E} {c d : K}
    (hz : HasValueAtInfinity E z c) (hw : HasValueAtInfinity E w d) (hd : d ≠ 0) :
    HasValueAtInfinity E (z / w) (c / d) := by
  simpa only [div_eq_mul_inv] using hz.mul (hw.inv hd)
end WeierstrassCurve.Velu

namespace WeierstrassCurve.Velu
open RatFunc
variable {K : Type*} [Field K] [CharZero K]

/-- The chord slope for translation has explicit quadratic coordinates. -/
theorem genericSlope_eq (E : WeierstrassCurve K) (u v : K) :
    (genericY E - algebraMap K _ v) / (genericX E - algebraMap K _ u) =
      (⟨(-C E.a₁ * X - C E.a₃ - 2 * C v) / (2 * (X - C u)),
        1 / (2 * (X - C u))⟩ : FunctionField E) := by
  apply (div_eq_iff (sub_ne_zero.mpr (genericX_ne_constant E u))).mpr
  ext <;> simp [genericX, genericY, liftX, liftY, QuadraticAlgebra.algebraMap_eq]
  all_goals field_simp [X_sub_C_ne_zero u]

set_option maxHeartbeats 800000 in
-- Expanding the chord coordinates clears a squared denominator.
/-- The translated generic x-coordinate has an explicit expansion at infinity. -/
theorem translateX_coordinates (E : WeierstrassCurve K) {u v : K}
    (hQ : E.toAffine.Equation u v) :
    translateX E u v =
      (⟨C u + C (3 * u ^ 2 + E.b₂ * u / 2 + E.b₄ / 2) / (X - C u) +
          C ((2 * v + E.a₁ * u + E.a₃) ^ 2) / (2 * (X - C u) ^ 2),
        -C (2 * v + E.a₁ * u + E.a₃) / (2 * (X - C u) ^ 2)⟩ : FunctionField E) := by
  have hq := congrArg (C : K →+* K⟮X⟯) ((Affine.equation_iff _ _).mp hQ)
  simp only [map_add, map_mul, map_pow] at hq
  unfold translateX
  rw [genericSlope_eq]
  ext <;>
    simp [Affine.addX, genericX, liftX, WeierstrassCurve.map, QuadraticAlgebra.algebraMap_eq,
      pow_two, cubicFunction_eq, b₂, b₄, b₆, map_div₀, map_ofNat]
  all_goals field_simp [X_sub_C_ne_zero u]
  · linear_combination -4 * hq
  · ring

/-- The translated x-coordinate has the abscissa of the translating point as its value. -/
theorem translateX_valueAtInfinity (E : WeierstrassCurve K) {u v : K}
    (hQ : E.toAffine.Equation u v) :
    HasValueAtInfinity E (translateX E u v) u := by
  rw [translateX_coordinates E hQ]
  have h1 : RatFunc.HasValueAtInfinity
      (C (3 * u ^ 2 + E.b₂ * u / 2 + E.b₄ / 2) / (X - C u)) 0 := by
    apply RatFunc.HasValueAtInfinity.of_degreeLE
    simpa only [pow_one, Nat.cast_one, sub_self, zero_sub] using
      (DegreeLE.C (3 * u ^ 2 + E.b₂ * u / 2 + E.b₄ / 2)).div_X_sub_C_pow u 1
  have h2 : RatFunc.HasValueAtInfinity
      (C ((2 * v + E.a₁ * u + E.a₃) ^ 2) / (2 * (X - C u) ^ 2)) 0 := by
    apply RatFunc.HasValueAtInfinity.of_degreeLE
    have h : DegreeLE
        (C ((2 * v + E.a₁ * u + E.a₃) ^ 2 / 2) / (X - C u) ^ 2) (-2) := by
      convert (DegreeLE.C ((2 * v + E.a₁ * u + E.a₃) ^ 2 / 2)).div_X_sub_C_pow u 2 using 1
      norm_num
    simpa only [map_div₀, map_ofNat, div_mul_eq_div_div] using h.mono (by omega)
  constructor
  · simpa using ((RatFunc.HasValueAtInfinity.C u).add h1).add h2
  · have h : DegreeLE
        (C (-(2 * v + E.a₁ * u + E.a₃) / 2) / (X - C u) ^ 2) (-2) := by
      simpa using (DegreeLE.C (-(2 * v + E.a₁ * u + E.a₃) / 2)).div_X_sub_C_pow u 2
    simpa only [map_div₀, map_neg, map_ofNat, div_mul_eq_div_div] using h
end WeierstrassCurve.Velu

namespace WeierstrassCurve.Velu
open RatFunc
variable {K : Type*} [Field K] [CharZero K]

set_option maxHeartbeats 1000000 in
-- The completed y-coordinate expands to cubic denominators in the quadratic field.
/-- The translated completed y-coordinate has an explicit expansion at infinity. -/
theorem translate_completedY_coordinates (E : WeierstrassCurve K) {u v : K}
    (hQ : E.toAffine.Equation u v) :
    2 * translateY E u v + algebraMap K _ E.a₁ * translateX E u v +
        algebraMap K (FunctionField E) E.a₃ =
      (⟨C (2 * v + E.a₁ * u + E.a₃) +
          C ((2 * v + E.a₁ * u + E.a₃) * (6 * u + E.b₂ / 2)) / (X - C u) +
          C (3 * (2 * v + E.a₁ * u + E.a₃) *
            (3 * u ^ 2 + E.b₂ * u / 2 + E.b₄ / 2)) / (X - C u) ^ 2 +
          C ((2 * v + E.a₁ * u + E.a₃) ^ 3) / (X - C u) ^ 3,
        -C (3 * u ^ 2 + E.b₂ * u / 2 + E.b₄ / 2) / (X - C u) ^ 2 -
          C ((2 * v + E.a₁ * u + E.a₃) ^ 2) / (X - C u) ^ 3⟩ : FunctionField E) := by
  have hq := congrArg (C : K →+* K⟮X⟯) ((Affine.equation_iff _ _).mp hQ)
  simp only [map_add, map_mul, map_pow] at hq
  have hy : translateY E u v =
      -((genericY E - algebraMap K _ v) / (genericX E - algebraMap K _ u) *
        (translateX E u v - genericX E) + genericY E) -
        algebraMap K _ E.a₁ * translateX E u v - algebraMap K _ E.a₃ := rfl
  rw [hy, genericSlope_eq, translateX_coordinates E hQ]
  ext <;>
    simp [genericX, genericY, liftX, liftY,
      QuadraticAlgebra.algebraMap_eq, cubicFunction_eq, b₂, b₄, b₆, map_div₀, map_ofNat]
  all_goals field_simp [X_sub_C_ne_zero u]
  · linear_combination -4 * (2 * C v + C E.a₁ * C u + C E.a₃) * hq
  · ring
end WeierstrassCurve.Velu

namespace WeierstrassCurve.Velu
open RatFunc
open scoped Polynomial
variable {K : Type*} [Field K] [CharZero K] {E : WeierstrassCurve K}

/-- Evaluation at infinity respects natural powers. -/
theorem HasValueAtInfinity.pow {z : FunctionField E} {c : K}
    (hz : HasValueAtInfinity E z c) (n : ℕ) :
    HasValueAtInfinity E (z ^ n) (c ^ n) := by
  induction n with
  | zero => simpa using HasValueAtInfinity.constant E (1 : K)
  | succ n ih => simpa only [pow_succ] using ih.mul hz

/-- Polynomial substitution respects evaluation at infinity. -/
theorem HasValueAtInfinity.polynomial
    (σ : K⟮X⟯ →ₐ[K] FunctionField E) {c : K}
    (hx : HasValueAtInfinity E (σ X) c) (p : K[X]) :
    HasValueAtInfinity E (σ (algebraMap K[X] K⟮X⟯ p)) (p.eval c) := by
  have hc (a : K) : σ (C a) = algebraMap K _ a := σ.commutes a
  induction p using Polynomial.induction_on' with
  | add p q hp hq => simpa only [map_add, Polynomial.eval_add] using hp.add hq
  | monomial n a =>
    simpa only [← Polynomial.C_mul_X_pow_eq_monomial, map_mul, map_pow,
      RatFunc.algebraMap_C, RatFunc.algebraMap_X, hc,
      Polynomial.eval_mul, Polynomial.eval_C, Polynomial.eval_pow, Polynomial.eval_X] using
      (HasValueAtInfinity.constant E a).mul (hx.pow n)

/-- Rational substitution respects evaluation at infinity at a regular argument. -/
theorem HasValueAtInfinity.rational
    (σ : K⟮X⟯ →ₐ[K] FunctionField E) {c : K}
    (hx : HasValueAtInfinity E (σ X) c) (f : K⟮X⟯) (hf : RegularAt c f) :
    HasValueAtInfinity E (σ f) (RatFunc.eval (RingHom.id K) c f) := by
  have hn := hx.polynomial σ f.num
  have hd := hx.polynomial σ f.denom
  have h := hn.div hd hf
  rw [← map_div₀, f.num_div_denom] at h
  simpa only [RatFunc.eval, Polynomial.eval₂_id] using h
end WeierstrassCurve.Velu

namespace RatFunc
variable {K : Type*} [Field K]
/-- A constant divided by a positive shifted power vanishes at infinity. -/
theorem HasValueAtInfinity.coefficient_div (a u : K) (n : ℕ) (hn : 1 ≤ n) :
    HasValueAtInfinity (RatFunc.C a / (X - RatFunc.C u) ^ n) 0 := by
  apply HasValueAtInfinity.of_degreeLE
  exact ((DegreeLE.C a).div_X_sub_C_pow u n).mono (by omega)
end RatFunc

namespace WeierstrassCurve.Velu
open RatFunc
variable {K : Type*} [Field K] [CharZero K]

/-- The translated completed y-coordinate has the expected value at infinity. -/
theorem translate_completedY_valueAtInfinity (E : WeierstrassCurve K) {u v : K}
    (hQ : E.toAffine.Equation u v) :
    HasValueAtInfinity E
      (2 * translateY E u v + algebraMap K _ E.a₁ * translateX E u v +
        algebraMap K (FunctionField E) E.a₃) (2 * v + E.a₁ * u + E.a₃) := by
  rw [translate_completedY_coordinates E hQ]
  constructor
  · simpa only [pow_one, add_zero] using
      (((RatFunc.HasValueAtInfinity.C (2 * v + E.a₁ * u + E.a₃)).add
        (RatFunc.HasValueAtInfinity.coefficient_div
          ((2 * v + E.a₁ * u + E.a₃) * (6 * u + E.b₂ / 2)) u 1 (by decide))).add
        (RatFunc.HasValueAtInfinity.coefficient_div
          (3 * (2 * v + E.a₁ * u + E.a₃) *
            (3 * u ^ 2 + E.b₂ * u / 2 + E.b₄ / 2)) u 2 (by decide))).add
        (RatFunc.HasValueAtInfinity.coefficient_div
          ((2 * v + E.a₁ * u + E.a₃) ^ 3) u 3 (by decide))
  · have h1 : DegreeLE
        (-C (3 * u ^ 2 + E.b₂ * u / 2 + E.b₄ / 2) / (X - C u) ^ 2) (-2) := by
      simpa only [neg_div, zero_sub, Nat.cast_ofNat] using
        ((DegreeLE.C (3 * u ^ 2 + E.b₂ * u / 2 + E.b₄ / 2)).div_X_sub_C_pow u 2).neg
    have h2 : DegreeLE
        (C ((2 * v + E.a₁ * u + E.a₃) ^ 2) / (X - C u) ^ 3) (-3) := by
      simpa only [zero_sub, Nat.cast_ofNat] using
        (DegreeLE.C ((2 * v + E.a₁ * u + E.a₃) ^ 2)).div_X_sub_C_pow u 3
    exact h1.sub (h2.mono (by omega))

/-- The translated y-coordinate has the ordinate of the translating point as its value. -/
theorem translateY_valueAtInfinity (E : WeierstrassCurve K) {u v : K}
    (hQ : E.toAffine.Equation u v) : HasValueAtInfinity E (translateY E u v) v := by
  have h := (((translate_completedY_valueAtInfinity E hQ).sub
    ((HasValueAtInfinity.constant E E.a₁).mul (translateX_valueAtInfinity E hQ))).sub
    (HasValueAtInfinity.constant E E.a₃)).div
    (HasValueAtInfinity.constant E (2 : K)) (by norm_num)
  convert h using 1
  · simp only [map_ofNat]
    ring
  · ring
end WeierstrassCurve.Velu
