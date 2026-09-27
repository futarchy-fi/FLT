/-
Copyright (c) 2026 krandder. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: krandder
-/
module

public import FLT.FreyCurve.Serre.VeluInfinity

/-!
# Identifying the generic translation defect

Evaluation at infinity identifies the constant difference of the translated
Vélu coordinates. Specialization to ordinary points is a separate step.
-/

@[expose] public section

namespace WeierstrassCurve.Velu
open RatFunc
variable {K : Type*} [Field K] [CharZero K]

/-- The x-coordinate of a lifted rational point translated by a base-field point. -/
noncomputable def liftTranslateX (E E' : WeierstrassCurve K) (f g : K⟮X⟯) (u v : K) :
    FunctionField E :=
  (E'.map (algebraMap K _)).toAffine.addX (liftX E f) (algebraMap K _ u)
    ((liftY E E' f g - algebraMap K _ v) / (liftX E f - algebraMap K _ u))

/-- The y-coordinate of a lifted rational point translated by a base-field point. -/
noncomputable def liftTranslateY (E E' : WeierstrassCurve K) (f g : K⟮X⟯) (u v : K) :
    FunctionField E :=
  (E'.map (algebraMap K _)).toAffine.addY (liftX E f) (algebraMap K _ u) (liftY E E' f g)
    ((liftY E E' f g - algebraMap K _ v) / (liftX E f - algebraMap K _ u))

omit [CharZero K] in
/-- A nonzero rational difference stays nonzero in the quadratic field. -/
theorem liftX_ne_constant (E : WeierstrassCurve K) (f : K⟮X⟯) (u : K)
    (hf : f - C u ≠ 0) : liftX E f ≠ algebraMap K (FunctionField E) u := by
  intro h
  exact hf (sub_eq_zero.mpr (congrArg QuadraticAlgebra.re h))

/-- The slope from a lifted rational point has explicit quadratic coordinates. -/
theorem liftSlope_eq (E E' : WeierstrassCurve K) (f g : K⟮X⟯) (u v : K)
    (hf : f - C u ≠ 0) :
    (liftY E E' f g - algebraMap K _ v) / (liftX E f - algebraMap K _ u) =
      (⟨(-C E'.a₁ * f - C E'.a₃ - 2 * C v) / (2 * (f - C u)),
        g / (2 * (f - C u))⟩ : FunctionField E) := by
  apply (div_eq_iff (sub_ne_zero.mpr (liftX_ne_constant E f u hf))).mpr
  ext <;> simp [liftX, liftY, QuadraticAlgebra.algebraMap_eq]
  all_goals field_simp [hf]

set_option maxHeartbeats 800000 in
-- Clearing the chord denominators produces a large polynomial identity.
/-- The x-coordinate of a translated rational lift has explicit quadratic coordinates. -/
theorem liftTranslateX_coordinates (E E' : WeierstrassCurve K) (f g : K⟮X⟯)
    (heq : cubicFunction E * g ^ 2 =
      4 * f ^ 3 + C E'.b₂ * f ^ 2 + 2 * C E'.b₄ * f + C E'.b₆)
    {u v : K} (hQ : E'.toAffine.Equation u v) (hf : f - C u ≠ 0) :
    liftTranslateX E E' f g u v =
      (⟨C u + C (3 * u ^ 2 + E'.b₂ * u / 2 + E'.b₄ / 2) / (f - C u) +
          C ((2 * v + E'.a₁ * u + E'.a₃) ^ 2) / (2 * (f - C u) ^ 2),
        -g * C (2 * v + E'.a₁ * u + E'.a₃) / (2 * (f - C u) ^ 2)⟩ : FunctionField E) := by
  have hq := congrArg (C : K →+* K⟮X⟯) ((Affine.equation_iff _ _).mp hQ)
  simp only [map_add, map_mul, map_pow] at hq
  simp only [b₂, b₄, b₆, map_add, map_mul, map_pow, map_ofNat] at heq
  unfold liftTranslateX
  rw [liftSlope_eq E E' f g u v hf]
  ext <;>
    simp [Affine.addX, liftX, WeierstrassCurve.map, QuadraticAlgebra.algebraMap_eq,
      pow_two, b₂, b₄, map_div₀, map_ofNat]
  all_goals field_simp [hf]
  · linear_combination heq - 4 * hq
  · ring

set_option maxHeartbeats 1000000 in
-- The completed y-coordinate expands to cubic denominators.
/-- The completed y-coordinate of a translated lift has an explicit expansion. -/
theorem liftTranslate_completedY_coordinates (E E' : WeierstrassCurve K) (f g : K⟮X⟯)
    (heq : cubicFunction E * g ^ 2 =
      4 * f ^ 3 + C E'.b₂ * f ^ 2 + 2 * C E'.b₄ * f + C E'.b₆)
    {u v : K} (hQ : E'.toAffine.Equation u v) (hf : f - C u ≠ 0) :
    2 * liftTranslateY E E' f g u v + algebraMap K _ E'.a₁ * liftTranslateX E E' f g u v +
        algebraMap K (FunctionField E) E'.a₃ =
      (⟨C (2 * v + E'.a₁ * u + E'.a₃) +
          C ((2 * v + E'.a₁ * u + E'.a₃) * (6 * u + E'.b₂ / 2)) / (f - C u) +
          C (3 * (2 * v + E'.a₁ * u + E'.a₃) *
            (3 * u ^ 2 + E'.b₂ * u / 2 + E'.b₄ / 2)) / (f - C u) ^ 2 +
          C ((2 * v + E'.a₁ * u + E'.a₃) ^ 3) / (f - C u) ^ 3,
        g * (-C (3 * u ^ 2 + E'.b₂ * u / 2 + E'.b₄ / 2) / (f - C u) ^ 2 -
          C ((2 * v + E'.a₁ * u + E'.a₃) ^ 2) / (f - C u) ^ 3)⟩ : FunctionField E) := by
  have hq := congrArg (C : K →+* K⟮X⟯) ((Affine.equation_iff _ _).mp hQ)
  simp only [map_add, map_mul, map_pow] at hq
  have hy : liftTranslateY E E' f g u v =
      -((liftY E E' f g - algebraMap K _ v) / (liftX E f - algebraMap K _ u) *
        (liftTranslateX E E' f g u v - liftX E f) + liftY E E' f g) -
        algebraMap K _ E'.a₁ * liftTranslateX E E' f g u v - algebraMap K _ E'.a₃ := rfl
  rw [hy, liftSlope_eq E E' f g u v hf, liftTranslateX_coordinates E E' f g heq hQ hf]
  simp only [b₂, b₄, b₆, map_add, map_mul, map_pow, map_ofNat] at heq
  ext <;>
    simp [liftX, liftY, QuadraticAlgebra.algebraMap_eq, b₂, b₄, map_div₀, map_ofNat]
  all_goals field_simp [hf]
  · linear_combination (2 * C v + C E'.a₁ * C u + C E'.a₃) * (heq - 4 * hq)
  · ring
end WeierstrassCurve.Velu

namespace RatFunc
variable {K : Type*} [Field K]

/-- A decaying reciprocal gives degree bounds for constant numerators. -/
theorem DegreeLE.const_div_pow (a : K) {d : K⟮X⟯}
    (hd : DegreeLE d⁻¹ (-1)) (n : ℕ) :
    DegreeLE (RatFunc.C a / d ^ n) (-(n : ℤ)) := by
  simpa [div_eq_mul_inv] using (DegreeLE.C a).mul (hd.pow n)

/-- Positive reciprocal powers of a function with a pole vanish at infinity. -/
theorem HasValueAtInfinity.coefficient_div_of_inv (a : K) {d : K⟮X⟯}
    (hd : DegreeLE d⁻¹ (-1)) (n : ℕ) (hn : 1 ≤ n) :
    HasValueAtInfinity (RatFunc.C a / d ^ n) 0 :=
  HasValueAtInfinity.of_degreeLE ((DegreeLE.const_div_pow a hd n).mono (by omega))
end RatFunc

namespace WeierstrassCurve.Velu
open RatFunc
variable {K : Type*} [Field K] [CharZero K]

/-- The translated lifted x-coordinate evaluates to the translating abscissa. -/
theorem liftTranslateX_valueAtInfinity (E E' : WeierstrassCurve K) (f g : K⟮X⟯)
    (heq : cubicFunction E * g ^ 2 =
      4 * f ^ 3 + C E'.b₂ * f ^ 2 + 2 * C E'.b₄ * f + C E'.b₆)
    {u v : K} (hQ : E'.toAffine.Equation u v) (hf : f - C u ≠ 0)
    (hd : DegreeLE (f - C u)⁻¹ (-1)) (hg : DegreeLE g 0) :
    HasValueAtInfinity E (liftTranslateX E E' f g u v) u := by
  rw [liftTranslateX_coordinates E E' f g heq hQ hf]
  have h1 := RatFunc.HasValueAtInfinity.coefficient_div_of_inv
    (3 * u ^ 2 + E'.b₂ * u / 2 + E'.b₄ / 2) hd 1 (by decide)
  have h2 := RatFunc.HasValueAtInfinity.coefficient_div_of_inv
    ((2 * v + E'.a₁ * u + E'.a₃) ^ 2 / 2) hd 2 (by decide)
  constructor
  · convert ((RatFunc.HasValueAtInfinity.C u).add h1).add h2 using 1
    · simp only [pow_one, map_div₀, map_ofNat, div_mul_eq_div_div]
    · simp
  · have hi := hg.mul (DegreeLE.const_div_pow
      (-(2 * v + E'.a₁ * u + E'.a₃) / 2) hd 2)
    convert hi using 1
    · simp only [map_div₀, map_neg, map_ofNat]
      field_simp [hf]
    · norm_num

/-- The translated lifted completed ordinate has the expected value. -/
theorem liftTranslate_completedY_valueAtInfinity (E E' : WeierstrassCurve K)
    (f g : K⟮X⟯)
    (heq : cubicFunction E * g ^ 2 =
      4 * f ^ 3 + C E'.b₂ * f ^ 2 + 2 * C E'.b₄ * f + C E'.b₆)
    {u v : K} (hQ : E'.toAffine.Equation u v) (hf : f - C u ≠ 0)
    (hd : DegreeLE (f - C u)⁻¹ (-1)) (hg : DegreeLE g 0) :
    HasValueAtInfinity E
      (2 * liftTranslateY E E' f g u v +
        algebraMap K _ E'.a₁ * liftTranslateX E E' f g u v +
        algebraMap K (FunctionField E) E'.a₃) (2 * v + E'.a₁ * u + E'.a₃) := by
  rw [liftTranslate_completedY_coordinates E E' f g heq hQ hf]
  constructor
  · simpa only [pow_one, add_zero] using
      (((RatFunc.HasValueAtInfinity.C (2 * v + E'.a₁ * u + E'.a₃)).add
        (RatFunc.HasValueAtInfinity.coefficient_div_of_inv
          ((2 * v + E'.a₁ * u + E'.a₃) * (6 * u + E'.b₂ / 2)) hd 1 (by decide))).add
        (RatFunc.HasValueAtInfinity.coefficient_div_of_inv
          (3 * (2 * v + E'.a₁ * u + E'.a₃) *
            (3 * u ^ 2 + E'.b₂ * u / 2 + E'.b₄ / 2)) hd 2 (by decide))).add
        (RatFunc.HasValueAtInfinity.coefficient_div_of_inv
          ((2 * v + E'.a₁ * u + E'.a₃) ^ 3) hd 3 (by decide))
  · have h1 : DegreeLE
        (-C (3 * u ^ 2 + E'.b₂ * u / 2 + E'.b₄ / 2) / (f - C u) ^ 2) (-2) := by
      simpa only [neg_div, Nat.cast_ofNat] using
        (DegreeLE.const_div_pow (3 * u ^ 2 + E'.b₂ * u / 2 + E'.b₄ / 2) hd 2).neg
    have h2 : DegreeLE
        (C ((2 * v + E'.a₁ * u + E'.a₃) ^ 2) / (f - C u) ^ 3) (-3) := by
      simpa only [Nat.cast_ofNat] using
        DegreeLE.const_div_pow ((2 * v + E'.a₁ * u + E'.a₃) ^ 2) hd 3
    simpa using hg.mul (h1.sub (h2.mono (by omega)))

/-- The translated lifted y-coordinate evaluates to the translating ordinate. -/
theorem liftTranslateY_valueAtInfinity (E E' : WeierstrassCurve K) (f g : K⟮X⟯)
    (heq : cubicFunction E * g ^ 2 =
      4 * f ^ 3 + C E'.b₂ * f ^ 2 + 2 * C E'.b₄ * f + C E'.b₆)
    {u v : K} (hQ : E'.toAffine.Equation u v) (hf : f - C u ≠ 0)
    (hd : DegreeLE (f - C u)⁻¹ (-1)) (hg : DegreeLE g 0) :
    HasValueAtInfinity E (liftTranslateY E E' f g u v) v := by
  have h := (((liftTranslate_completedY_valueAtInfinity E E' f g heq hQ hf hd hg).sub
    ((HasValueAtInfinity.constant E E'.a₁).mul
      (liftTranslateX_valueAtInfinity E E' f g heq hQ hf hd hg))).sub
    (HasValueAtInfinity.constant E E'.a₃)).div
    (HasValueAtInfinity.constant E (2 : K)) (by norm_num)
  convert h using 1
  · simp only [map_ofNat]
    ring
  · ring
end WeierstrassCurve.Velu
namespace WeierstrassCurve.Velu
open RatFunc
variable {K : Type*} [Field K] [CharZero K] [DecidableEq K]
variable (E : WeierstrassCurve K) [E.IsElliptic]
variable (G : AddSubgroup E.toAffine.Point) [Fintype G]

/-- The translated Vélu x-coordinate evaluates to the affine coordinate sum. -/
theorem translated_imageX_valueAtInfinity
    (hodd : ∀ Q : G, Q ≠ 0 → Q ≠ -Q)
    {u v : K} (hQ : E.toAffine.Nonsingular u v)
    (hQG : Affine.Point.some u v hQ ∉ G) :
    HasValueAtInfinity E
      (imageX E G (substitution _ (translateX_transcendental E hQ)))
      (xMap E G (.some u v hQ)) := by
  have hu := x_not_mem_kernelAbscissae E G hQ hQG
  have hx : HasValueAtInfinity E
      (substitution _ (translateX_transcendental E hQ) X) u := by
    simpa using translateX_valueAtInfinity E hQ.1
  have h := hx.rational (substitution _ (translateX_transcendental E hQ))
    (xFunction E G) (regular_eval_xFunction E G u hu).1
  rw [(regular_eval_xFunction E G u hu).2, ← xMap_eq_sum_abscissae E G hodd hQ hQG] at h
  exact h

/-- The translated Vélu y-coordinate evaluates to the affine coordinate sum. -/
theorem translated_imageY_valueAtInfinity
    (hodd : ∀ Q : G, Q ≠ 0 → Q ≠ -Q)
    {u v : K} (hQ : E.toAffine.Nonsingular u v)
    (hQG : Affine.Point.some u v hQ ∉ G) :
    HasValueAtInfinity E
      (imageY E G (substitution _ (translateX_transcendental E hQ)) (translateY E u v))
      (yMap E G (.some u v hQ)) := by
  let σ := substitution _ (translateX_transcendental E hQ)
  have hu := x_not_mem_kernelAbscissae E G hQ hQG
  have hx : HasValueAtInfinity E (σ X) u := by
    simpa [σ] using translateX_valueAtInfinity E hQ.1
  have hs : HasValueAtInfinity E (σ (slopeFunction E G)) (slopeFactor E G u) := by
    have h := hx.rational σ (slopeFunction E G) (regular_eval_slopeFunction E G u hu).1
    rw [(regular_eval_slopeFunction E G u hu).2,
      ← slopeFactor_eq_sum_abscissae E G hodd u] at h
    exact h
  have hy := translateY_valueAtInfinity E hQ.1
  have hmx := translated_imageX_valueAtInfinity E G hodd hQ hQG
  have h := ((hs.mul ((((HasValueAtInfinity.constant E (2 : K)).mul hy).add
    ((HasValueAtInfinity.constant E E.a₁).mul hx)).add
    (HasValueAtInfinity.constant E E.a₃))).sub
    ((HasValueAtInfinity.constant E E.a₁).mul hmx)).sub
    (HasValueAtInfinity.constant E E.a₃)
  have hdiv := h.div (HasValueAtInfinity.constant E (2 : K)) (by norm_num)
  convert hdiv using 1
  · simp only [imageY, σ, map_ofNat]
  · have hc := completed_yMap E G hQ hQG
    linear_combination hc / 2
end WeierstrassCurve.Velu
namespace WeierstrassCurve.Velu
open RatFunc
open scoped WeierstrassCurve.Affine
variable {K : Type*} [Field K] [CharZero K] [DecidableEq K]
variable (E : WeierstrassCurve K) (G : AddSubgroup E.toAffine.Point) [Fintype G]

omit [CharZero K] in
/-- The rational Vélu slope has no pole at infinity. -/
theorem degreeLE_slopeFunction : DegreeLE (slopeFunction E G) 0 := by
  unfold slopeFunction
  have h1 : DegreeLE (1 : K⟮X⟯) 0 := by simpa using DegreeLE.natCast (K := K) 1
  apply h1.add
  exact (DegreeLE.sum (kernelAbscissae E G) _ (-2)
    (fun u _ => degreeLE_poleSlope _ _ _)).mono (by omega)

omit [CharZero K] in
/-- Every reciprocal constant shift of the Vélu x-function vanishes at infinity. -/
theorem degreeLE_inv_xFunction_sub_C (a : K) :
    DegreeLE (xFunction E G - C a)⁻¹ (-1) := by
  right
  rw [intDegree_inv]
  have h := xFunction_sub_C_not_degreeLE E G a
  have hd : ¬ (xFunction E G - C a).intDegree ≤ 0 := fun hh => h (Or.inr hh)
  omega

/-- The rational Vélu coordinates satisfy the target completed cubic equation. -/
theorem velu_rational_cubic
    (hodd : ∀ Q : G, Q ≠ 0 → Q ≠ -Q) :
    cubicFunction E * slopeFunction E G ^ 2 =
      4 * xFunction E G ^ 3 + C (curve E G).b₂ * xFunction E G ^ 2 +
        2 * C (curve E G).b₄ * xFunction E G + C (curve E G).b₆ := by
  rw [cubicFunction_eq]
  convert rational_equation_coefficients E G hodd using 1
  simp only [curve, b₂, b₄, b₆, map_add, map_sub, map_mul, map_pow, map_ofNat]
  ring

open Classical in
/-- Vélu's generic translation defect equals the image of the translating point. -/
theorem translated_image_eq_add [E.IsElliptic]
    (hodd : ∀ Q : G, Q ≠ 0 → Q ≠ -Q)
    {u v : K} (hQ : E.toAffine.Nonsingular u v)
    (hQG : Affine.Point.some u v hQ ∉ G) :
    let P := Affine.Point.some
      (imageX E G (substitution _ (translateX_transcendental E hQ)))
      (imageY E G (substitution _ (translateX_transcendental E hQ)) (translateY E u v))
      (translated_image_nonsingular E G hodd hQ)
    let R := Affine.Point.some (liftX E (xFunction E G))
      (liftY E (curve E G) (xFunction E G) (slopeFunction E G))
      (velu_lift_nonsingular E G hodd)
    ∃ h : (curve E G).toAffine.Nonsingular
        (xMap E G (.some u v hQ)) (yMap E G (.some u v hQ)),
      P = R + Affine.Point.some
        (algebraMap K _ (xMap E G (.some u v hQ)))
        (algebraMap K _ (yMap E G (.some u v hQ)))
        ((Affine.map_nonsingular (curve E G).toAffine
          (algebraMap K (FunctionField E)).injective _ _).mpr h) := by
  classical
  rcases translated_image_difference_constant E G hodd hQ with hsame | ⟨a, b, hab, hdiff⟩
  · exfalso
    have hx := congrArg xCoord hsame
    simp only [xCoord] at hx
    have hlim := translated_imageX_valueAtInfinity E G hodd hQ hQG
    rw [hx] at hlim
    apply xFunction_sub_C_not_degreeLE E G 0
    simpa [liftX] using hlim.1.degreeLE
  · have hf : xFunction E G - C a ≠ 0 :=
      fun hz => xFunction_sub_C_not_degreeLE E G a (Or.inl hz)
    have hxa := liftX_ne_constant E (xFunction E G) a hf
    have hp := (sub_eq_iff_eq_add).mp hdiff
    rw [add_comm, Affine.Point.add_of_X_ne hxa] at hp
    have hx := congrArg xCoord hp
    have hy := congrArg yCoord hp
    simp only [xCoord, Affine.slope_of_X_ne hxa] at hx
    simp only [yCoord, Affine.slope_of_X_ne hxa] at hy
    change imageX E G (substitution _ (translateX_transcendental E hQ)) =
      liftTranslateX E (curve E G) (xFunction E G) (slopeFunction E G) a b at hx
    change imageY E G (substitution _ (translateX_transcendental E hQ)) (translateY E u v) =
      liftTranslateY E (curve E G) (xFunction E G) (slopeFunction E G) a b at hy
    have hlimx := translated_imageX_valueAtInfinity E G hodd hQ hQG
    have hlimy := translated_imageY_valueAtInfinity E G hodd hQ hQG
    rw [hx] at hlimx
    rw [hy] at hlimy
    have ha := hlimx.unique (liftTranslateX_valueAtInfinity E (curve E G)
      (xFunction E G) (slopeFunction E G) (velu_rational_cubic E G hodd) hab.1 hf
      (degreeLE_inv_xFunction_sub_C E G a) (degreeLE_slopeFunction E G))
    have hb := hlimy.unique (liftTranslateY_valueAtInfinity E (curve E G)
      (xFunction E G) (slopeFunction E G) (velu_rational_cubic E G hodd) hab.1 hf
      (degreeLE_inv_xFunction_sub_C E G a) (degreeLE_slopeFunction E G))
    subst a
    subst b
    exact ⟨hab, (sub_eq_iff_eq_add').mp hdiff⟩
end WeierstrassCurve.Velu
