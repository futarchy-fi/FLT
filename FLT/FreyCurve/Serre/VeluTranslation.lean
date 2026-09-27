/-
Copyright (c) 2026 krandder. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: krandder
-/
module

public import FLT.FreyCurve.Serre.VeluFunctionField
public import Mathlib.FieldTheory.Perfect

/-!
# Translation and substitution in Vélu's construction

Translation of the generic point preserves the invariant derivation. Its
x-coordinate is transcendental, so rational functions can be substituted there.
The substituted Vélu coordinates satisfy the target equation and preserve the
same derivation. Their translation defect is a base-field point, including the
case of coincident x-coordinates. Identifying this constant remains necessary
to deduce additivity.
-/

@[expose] public section


namespace WeierstrassCurve.Affine
variable {K L : Type*} [Field K] [Field L] [Algebra K L]

-- The cleared chord identity has high-degree polynomial terms.
set_option maxRecDepth 4096 in
set_option maxHeartbeats 800000 in
-- Clearing the chord denominators requires a large polynomial normalization.
/-- The y-coordinate of a chord sum adds the two invariant velocities. -/
theorem derivation_addY (E : WeierstrassCurve K) (d : Derivation K L L)
    {x y u v r s : L}
    (hP : (E.map (algebraMap K L)).toAffine.Equation x y)
    (hQ : (E.map (algebraMap K L)).toAffine.Equation u v)
    (hxu : x ≠ u)
    (hx : d x = r * (2 * y + algebraMap K L E.a₁ * x + algebraMap K L E.a₃))
    (hy : d y = r * (3 * x ^ 2 + 2 * algebraMap K L E.a₂ * x + algebraMap K L E.a₄ -
      algebraMap K L E.a₁ * y))
    (hu : d u = s * (2 * v + algebraMap K L E.a₁ * u + algebraMap K L E.a₃))
    (hv : d v = s * (3 * u ^ 2 + 2 * algebraMap K L E.a₂ * u + algebraMap K L E.a₄ -
      algebraMap K L E.a₁ * v)) :
    d ((E.map (algebraMap K L)).toAffine.addY x u y ((y - v) / (x - u))) =
      (r + s) * (3 * ((E.map (algebraMap K L)).toAffine.addX x u ((y - v) / (x - u))) ^ 2 +
        2 * algebraMap K L E.a₂ *
          (E.map (algebraMap K L)).toAffine.addX x u ((y - v) / (x - u)) +
        algebraMap K L E.a₄ - algebraMap K L E.a₁ *
          (E.map (algebraMap K L)).toAffine.addY x u y ((y - v) / (x - u))) := by
  have hp := (equation_iff _ _).mp hP
  have hq := (equation_iff _ _).mp hQ
  dsimp [WeierstrassCurve.map] at hp hq
  have hl : d ((y - v) / (x - u)) =
      ((x - u) * (d y - d v) - (y - v) * (d x - d u)) / (x - u) ^ 2 := by
    rw [d.leibniz_div]
    simp only [map_sub, smul_eq_mul, div_eq_mul_inv, inv_pow]
    ring
  have hdX := derivation_addX E d hP hQ hxu hx hy hu hv
  unfold addY negY negAddY
  simp only [map_sub, map_add, map_neg, Derivation.leibniz, smul_eq_mul]
  rw [hdX, hl, hx, hy, hu, hv]
  simp only [addX, addY, negAddY, negY, WeierstrassCurve.map,
    Derivation.map_algebraMap, mul_zero, sub_zero, add_zero]
  field_simp [sub_ne_zero.mpr hxu]
  linear_combination
    ((r - s) * ((y - v) ^ 2 + algebraMap K L E.a₁ * (x - u) * (y - v) -
        (algebraMap K L E.a₂ + 3 * u) * (x - u) ^ 2) +
      3 * s * (x - u) ^ 3) * (hp - hq)
end WeierstrassCurve.Affine

namespace Derivation
variable {K L : Type*} [Field K] [CharZero K] [Field L] [Algebra K L]

/-- A derivation vanishes on elements algebraic over a characteristic-zero base. -/
theorem map_eq_zero_of_isAlgebraic (d : Derivation K L L) {x : L}
    (hx : IsAlgebraic K x) : d x = 0 := by
  have h := congrArg d (minpoly.aeval K x)
  rw [d.map_aeval, map_zero, smul_eq_mul] at h
  exact (mul_eq_zero.mp h).resolve_left
    ((minpoly.irreducible hx.isIntegral).separable.aeval_derivative_ne_zero (minpoly.aeval K x))

/-- Nonzero derivative implies transcendence over the base. -/
theorem transcendental_of_map_ne_zero (d : Derivation K L L) {x : L} (hx : d x ≠ 0) :
    Transcendental K x := fun h => hx (d.map_eq_zero_of_isAlgebraic h)
end Derivation

namespace WeierstrassCurve.Affine
variable {K L : Type*} [Field K] [CharZero K] [Field L] [Algebra K L] [CharZero L]

/-- A nonsingular point moving with unit invariant velocity has transcendental x-coordinate. -/
theorem transcendental_of_normalized_derivation
    (E : WeierstrassCurve K) (d : Derivation K L L) {x y : L}
    (hP : (E.map (algebraMap K L)).toAffine.Nonsingular x y)
    (hx : d x = 2 * y + algebraMap K L E.a₁ * x + algebraMap K L E.a₃)
    (hy : d y = 3 * x ^ 2 + 2 * algebraMap K L E.a₂ * x + algebraMap K L E.a₄ -
      algebraMap K L E.a₁ * y) : Transcendental K x := by
  apply d.transcendental_of_map_ne_zero
  intro hz
  have hdy := derivation_y_eq_zero_of_x_eq_zero E d hP.1 hz
  have hs := hx.symm.trans hz
  have ht := hy.symm.trans hdy
  rcases ((nonsingular_iff' _ _).mp hP).2 with h | h
  · apply h
    dsimp [WeierstrassCurve.map]
    linear_combination -ht
  · exact h hs
end WeierstrassCurve.Affine

namespace WeierstrassCurve.Velu
open RatFunc
variable {K : Type*} [Field K] [CharZero K]

/-- The x-coordinate of the generic point. -/
noncomputable def genericX (E : WeierstrassCurve K) : FunctionField E := liftX E X
/-- The y-coordinate of the generic point. -/
noncomputable def genericY (E : WeierstrassCurve K) : FunctionField E := liftY E E X 1

/-- The generic coordinates satisfy the source equation. -/
theorem generic_equation (E : WeierstrassCurve K) :
    (E.map (algebraMap K (FunctionField E))).toAffine.Equation (genericX E) (genericY E) := by
  apply lift_equation
  simpa using cubicFunction_eq E

/-- The generic x-coordinate has unit invariant velocity. -/
theorem generic_derivation_x (E : WeierstrassCurve K) :
    quadraticDerivation (cubicFunction E) (genericX E) =
      2 * genericY E + algebraMap K _ E.a₁ * genericX E + algebraMap K _ E.a₃ := by
  simpa [genericX, genericY] using derivation_liftX E E X

/-- The generic y-coordinate has unit invariant velocity. -/
theorem generic_derivation_y (E : WeierstrassCurve K) :
    quadraticDerivation (cubicFunction E) (genericY E) =
      3 * genericX E ^ 2 + 2 * algebraMap K _ E.a₂ * genericX E + algebraMap K _ E.a₄ -
        algebraMap K _ E.a₁ * genericY E := by
  simpa using Affine.derivation_y_of_equation E (quadraticDerivation (cubicFunction E))
    (generic_equation E) (v := 1) (by simpa using generic_derivation_x E)
    (lift_completedY_ne_zero E E X 1 one_ne_zero)

omit [CharZero K] in
/-- The generic x-coordinate differs from every base-field constant. -/
theorem genericX_ne_constant (E : WeierstrassCurve K) (u : K) :
    genericX E ≠ algebraMap K (FunctionField E) u := by
  intro h
  have hh := congrArg QuadraticAlgebra.re h
  change X = C u at hh
  exact X_sub_C_ne_zero u (sub_eq_zero.mpr hh)

/-- The x-coordinate of the generic point translated by an affine point. -/
noncomputable def translateX (E : WeierstrassCurve K) (u v : K) : FunctionField E :=
  (E.map (algebraMap K _)).toAffine.addX (genericX E) (algebraMap K _ u)
    ((genericY E - algebraMap K _ v) / (genericX E - algebraMap K _ u))

/-- The y-coordinate of the generic point translated by an affine point. -/
noncomputable def translateY (E : WeierstrassCurve K) (u v : K) : FunctionField E :=
  (E.map (algebraMap K _)).toAffine.addY (genericX E) (algebraMap K _ u) (genericY E)
    ((genericY E - algebraMap K _ v) / (genericX E - algebraMap K _ u))

/-- Translation by a nonsingular affine point stays nonsingular. -/
theorem translate_nonsingular (E : WeierstrassCurve K) [E.IsElliptic] {u v : K}
    (hQ : E.toAffine.Nonsingular u v) :
    (E.map (algebraMap K (FunctionField E))).toAffine.Nonsingular
      (translateX E u v) (translateY E u v) := by
  classical
  have hp := Affine.equation_iff_nonsingular.mp (generic_equation E)
  have hq := (Affine.map_nonsingular E.toAffine
    (algebraMap K (FunctionField E)).injective u v).mpr hQ
  have h := Affine.nonsingular_add hp hq
    (fun h => genericX_ne_constant E u h.1)
  simpa only [translateX, translateY,
    Affine.slope_of_X_ne (genericX_ne_constant E u)] using h

/-- Translation preserves the invariant x-velocity. -/
theorem translate_derivation_x (E : WeierstrassCurve K) {u v : K}
    (hQ : E.toAffine.Equation u v) :
    quadraticDerivation (cubicFunction E) (translateX E u v) =
      2 * translateY E u v + algebraMap K _ E.a₁ * translateX E u v +
        algebraMap K _ E.a₃ := by
  have hq := hQ.map (algebraMap K (FunctionField E))
  simpa [translateX, translateY] using Affine.derivation_addX E
    (quadraticDerivation (cubicFunction E)) (generic_equation E) hq
    (genericX_ne_constant E u)
    (r := 1) (s := 0)
    (by simpa using generic_derivation_x E)
    (by simpa using generic_derivation_y E)
    (by simp) (by simp)

/-- Translation preserves the invariant y-velocity. -/
theorem translate_derivation_y (E : WeierstrassCurve K) {u v : K}
    (hQ : E.toAffine.Equation u v) :
    quadraticDerivation (cubicFunction E) (translateY E u v) =
      3 * translateX E u v ^ 2 + 2 * algebraMap K _ E.a₂ * translateX E u v +
        algebraMap K _ E.a₄ - algebraMap K _ E.a₁ * translateY E u v := by
  have hq := hQ.map (algebraMap K (FunctionField E))
  simpa [translateX, translateY] using Affine.derivation_addY E
    (quadraticDerivation (cubicFunction E)) (generic_equation E) hq
    (genericX_ne_constant E u)
    (r := 1) (s := 0)
    (by simpa using generic_derivation_x E)
    (by simpa using generic_derivation_y E)
    (by simp) (by simp)

/-- The translated x-coordinate admits rational substitution. -/
theorem translateX_transcendental (E : WeierstrassCurve K) [E.IsElliptic] {u v : K}
    (hQ : E.toAffine.Nonsingular u v) : Transcendental K (translateX E u v) :=
  Affine.transcendental_of_normalized_derivation E (quadraticDerivation (cubicFunction E))
    (translate_nonsingular E hQ) (translate_derivation_x E hQ.1) (translate_derivation_y E hQ.1)
end WeierstrassCurve.Velu
open scoped Polynomial
namespace RatFunc
variable {K L : Type*} [Field K] [Field L] [Algebra K L]

/-- Substitute a transcendental element into a rational function. -/
noncomputable def substitution (x : L) (hx : Transcendental K x) : K⟮X⟯ →ₐ[K] L :=
  (IntermediateField.val (IntermediateField.adjoin K {x})).comp
    (algEquivOfTranscendental x hx).toAlgHom

/-- Substitution sends the variable to the chosen element. -/
@[simp] theorem substitution_X (x : L) (hx : Transcendental K x) :
    substitution x hx X = x := by
  simp [substitution]

/-- Substitution fixes base-field constants. -/
@[simp] theorem substitution_C (x : L) (hx : Transcendental K x) (c : K) :
    substitution x hx (C c) = algebraMap K L c :=
  (substitution x hx).commutes c

/-- An algebra homomorphism on rational functions evaluates polynomial coefficients. -/
theorem map_polynomial_aeval (σ : K⟮X⟯ →ₐ[K] L) (p : K[X]) :
    σ (algebraMap K[X] K⟮X⟯ p) = Polynomial.aeval (σ X) p := by
  rw [Polynomial.aeval_algHom_apply, aeval_X_left_eq_algebraMap]

/-- The chain rule for a rational-function algebra homomorphism. -/
theorem derivation_chain (σ : K⟮X⟯ →ₐ[K] L) (d : Derivation K L L) (f : K⟮X⟯) :
    d (σ f) = σ (formalDerivation f) * d (σ X) := by
  have hp (p : K[X]) : d (σ (algebraMap K[X] K⟮X⟯ p)) =
      σ (algebraMap K[X] K⟮X⟯ p.derivative) * d (σ X) := by
    simp only [map_polynomial_aeval, d.map_aeval, smul_eq_mul]
  have hq : σ (algebraMap K[X] K⟮X⟯ f.denom) ≠ 0 :=
    (map_ne_zero σ).mpr (algebraMap_ne_zero f.denom_ne_zero)
  rw [formalDerivation_apply, formalDeriv]
  conv_lhs => rw [← f.num_div_denom]
  simp only [map_div₀, map_pow, map_sub, map_mul]
  rw [d.leibniz_div, hp, hp]
  simp only [smul_eq_mul]
  field_simp
end RatFunc

namespace WeierstrassCurve.Velu
open RatFunc
variable {K L : Type*} [Field K] [CharZero K] [DecidableEq K]
  [Field L] [CharZero L] [Algebra K L]
variable (E : WeierstrassCurve K) (G : AddSubgroup E.toAffine.Point) [Fintype G]

/-- The Vélu x-coordinate after rational substitution. -/
noncomputable def imageX (σ : K⟮X⟯ →ₐ[K] L) : L := σ (xFunction E G)
/-- The Vélu y-coordinate after rational substitution. -/
noncomputable def imageY (σ : K⟮X⟯ →ₐ[K] L) (y : L) : L :=
  (σ (slopeFunction E G) * (2 * y + algebraMap K L E.a₁ * σ X + algebraMap K L E.a₃) -
    algebraMap K L E.a₁ * imageX E G σ - algebraMap K L E.a₃) / 2

/-- Substituted Vélu coordinates satisfy the target equation. -/
theorem image_equation (hodd : ∀ Q : G, Q ≠ 0 → Q ≠ -Q)
    (σ : K⟮X⟯ →ₐ[K] L) (y : L)
    (hP : (E.map (algebraMap K L)).toAffine.Equation (σ X) y) :
    ((curve E G).map (algebraMap K L)).toAffine.Equation
      (imageX E G σ) (imageY E G σ y) := by
  have hc (c : K) : σ (RatFunc.C c) = algebraMap K L c := σ.commutes c
  have h := congrArg σ (rational_equation_coefficients E G hodd)
  simp only [map_add, map_sub, map_mul, map_pow, map_ofNat, hc] at h
  have hp := (Affine.equation_iff _ _).mp hP
  rw [Affine.equation_iff]
  dsimp [imageX, imageY, curve, WeierstrassCurve.map]
  simp only [map_sub, map_mul, map_ofNat, b₂, b₄, b₆, map_add, map_pow] at h ⊢
  dsimp [WeierstrassCurve.map] at hp
  linear_combination
    h / 4 + (σ (slopeFunction E G)) ^ 2 * hp

omit [CharZero K] in
/-- Substituted Vélu coordinates preserve invariant x-velocity. -/
theorem image_derivation_x (σ : K⟮X⟯ →ₐ[K] L) (d : Derivation K L L) (y : L)
    (hx : d (σ X) = 2 * y + algebraMap K L E.a₁ * σ X + algebraMap K L E.a₃) :
    d (imageX E G σ) =
      2 * imageY E G σ y + algebraMap K L (curve E G).a₁ * imageX E G σ +
        algebraMap K L (curve E G).a₃ := by
  rw [imageX, derivation_chain, derivation_xFunction, hx]
  dsimp [imageY, imageX, curve]
  ring

/-- The substituted completed y-coordinate is nonzero away from source two-torsion. -/
theorem image_completedY_ne_zero (σ : K⟮X⟯ →ₐ[K] L) (y : L)
    (hy : 2 * y + algebraMap K L E.a₁ * σ X + algebraMap K L E.a₃ ≠ 0) :
    2 * imageY E G σ y + algebraMap K L (curve E G).a₁ * imageX E G σ +
      algebraMap K L (curve E G).a₃ ≠ 0 := by
  have hd : σ (slopeFunction E G) ≠ 0 := (map_ne_zero σ).mpr (slopeFunction_ne_zero E G)
  convert mul_ne_zero hd hy using 1
  dsimp [imageY, imageX, curve]
  ring

/-- Substituted Vélu coordinates preserve invariant y-velocity. -/
theorem image_derivation_y (hodd : ∀ Q : G, Q ≠ 0 → Q ≠ -Q)
    (σ : K⟮X⟯ →ₐ[K] L) (d : Derivation K L L) (y : L)
    (hP : (E.map (algebraMap K L)).toAffine.Equation (σ X) y)
    (hx : d (σ X) = 2 * y + algebraMap K L E.a₁ * σ X + algebraMap K L E.a₃)
    (hy : 2 * y + algebraMap K L E.a₁ * σ X + algebraMap K L E.a₃ ≠ 0) :
    d (imageY E G σ y) =
      3 * imageX E G σ ^ 2 +
        2 * algebraMap K L (curve E G).a₂ * imageX E G σ +
        algebraMap K L (curve E G).a₄ -
        algebraMap K L (curve E G).a₁ * imageY E G σ y := by
  simpa using Affine.derivation_y_of_equation (curve E G) d
    (image_equation E G hodd σ y hP) (v := 1)
    (by simpa using image_derivation_x E G σ d y hx)
    (image_completedY_ne_zero E G σ y hy)

end WeierstrassCurve.Velu
namespace WeierstrassCurve.Velu
open RatFunc
variable {K : Type*} [Field K] [CharZero K] [DecidableEq K]
variable (E : WeierstrassCurve K) [E.IsElliptic]
variable (G : AddSubgroup E.toAffine.Point) [Fintype G]

omit [DecidableEq K] in
/-- The translated generic point is away from two-torsion. -/
theorem translate_completedY_ne_zero {u v : K} (hQ : E.toAffine.Nonsingular u v) :
    2 * translateY E u v + algebraMap K _ E.a₁ * translateX E u v +
      algebraMap K (FunctionField E) E.a₃ ≠ 0 := by
  intro hz
  have hd := (translate_derivation_x E hQ.1).trans hz
  obtain ⟨c, hc⟩ := (functionField_derivation_eq_zero_iff E _).mp hd
  apply translateX_transcendental E hQ
  rw [hc]
  exact isAlgebraic_algebraMap c

/-- Vélu's translated generic coordinates satisfy the target equation. -/
theorem translated_image_equation (hodd : ∀ Q : G, Q ≠ 0 → Q ≠ -Q)
    {u v : K} (hQ : E.toAffine.Nonsingular u v) :
    ((curve E G).map (algebraMap K (FunctionField E))).toAffine.Equation
      (imageX E G (substitution _ (translateX_transcendental E hQ)))
      (imageY E G (substitution _ (translateX_transcendental E hQ)) (translateY E u v)) := by
  apply image_equation E G hodd
  simpa using (translate_nonsingular E hQ).1

/-- The translated Vélu x-coordinate has unit invariant velocity. -/
theorem translated_image_derivation_x {u v : K} (hQ : E.toAffine.Nonsingular u v) :
    quadraticDerivation (cubicFunction E)
      (imageX E G (substitution _ (translateX_transcendental E hQ))) =
      2 * imageY E G (substitution _ (translateX_transcendental E hQ)) (translateY E u v) +
        algebraMap K _ (curve E G).a₁ *
          imageX E G (substitution _ (translateX_transcendental E hQ)) +
        algebraMap K _ (curve E G).a₃ := by
  apply image_derivation_x
  simpa using translate_derivation_x E hQ.1

/-- The translated Vélu y-coordinate has unit invariant velocity. -/
theorem translated_image_derivation_y (hodd : ∀ Q : G, Q ≠ 0 → Q ≠ -Q)
    {u v : K} (hQ : E.toAffine.Nonsingular u v) :
    quadraticDerivation (cubicFunction E)
      (imageY E G (substitution _ (translateX_transcendental E hQ)) (translateY E u v)) =
      3 * (imageX E G (substitution _ (translateX_transcendental E hQ))) ^ 2 +
        2 * algebraMap K _ (curve E G).a₂ *
          imageX E G (substitution _ (translateX_transcendental E hQ)) +
        algebraMap K _ (curve E G).a₄ -
        algebraMap K _ (curve E G).a₁ *
          imageY E G (substitution _ (translateX_transcendental E hQ)) (translateY E u v) := by
  apply image_derivation_y E G hodd
  · simpa using (translate_nonsingular E hQ).1
  · simpa using translate_derivation_x E hQ.1
  · simpa using translate_completedY_ne_zero E hQ
end WeierstrassCurve.Velu
namespace WeierstrassCurve.Velu
open RatFunc
open scoped WeierstrassCurve.Affine
variable {K : Type*} [Field K] [CharZero K]

open scoped Classical in
/-- Two points with equal unit invariant velocity differ by a base-field point. -/
theorem equal_velocity_difference_constant (E E' : WeierstrassCurve K)
    {x y u v : FunctionField E}
    (hP : (E'.map (algebraMap K (FunctionField E))).toAffine.Nonsingular x y)
    (hQ : (E'.map (algebraMap K (FunctionField E))).toAffine.Nonsingular u v)
    (hx : quadraticDerivation (cubicFunction E) x =
      2 * y + algebraMap K _ E'.a₁ * x + algebraMap K _ E'.a₃)
    (hy : quadraticDerivation (cubicFunction E) y =
      3 * x ^ 2 + 2 * algebraMap K _ E'.a₂ * x + algebraMap K _ E'.a₄ -
        algebraMap K _ E'.a₁ * y)
    (hu : quadraticDerivation (cubicFunction E) u =
      2 * v + algebraMap K _ E'.a₁ * u + algebraMap K _ E'.a₃)
    (hv : quadraticDerivation (cubicFunction E) v =
      3 * u ^ 2 + 2 * algebraMap K _ E'.a₂ * u + algebraMap K _ E'.a₄ -
        algebraMap K _ E'.a₁ * v) :
    (Affine.Point.some x y hP = Affine.Point.some u v hQ) ∨
    ∃ (a b : K) (h : E'.toAffine.Nonsingular a b),
      Affine.Point.some x y hP - Affine.Point.some u v hQ =
        Affine.Point.some (algebraMap K _ a) (algebraMap K _ b)
          ((Affine.map_nonsingular E'.toAffine
            (algebraMap K (FunctionField E)).injective a b).mpr h) := by
  classical
  by_cases hxu : x = u
  · left
    have hyv : y = v := by
      rw [hxu] at hx
      linear_combination (hu - hx) / 2
    subst x
    subst y
    rfl
  · right
    let vn := (E'.map (algebraMap K (FunctionField E))).toAffine.negY u v
    have hqn := ((E'.map (algebraMap K (FunctionField E))).toAffine.nonsingular_neg u v).mpr hQ
    have hun : quadraticDerivation (cubicFunction E) u =
        -(1 : FunctionField E) *
          (2 * vn + algebraMap K _ E'.a₁ * u + algebraMap K _ E'.a₃) := by
      rw [hu]
      dsimp [vn, Affine.negY, WeierstrassCurve.map]
      ring
    have hvn : quadraticDerivation (cubicFunction E) vn =
        -(1 : FunctionField E) *
          (3 * u ^ 2 + 2 * algebraMap K _ E'.a₂ * u + algebraMap K _ E'.a₄ -
            algebraMap K _ E'.a₁ * vn) := by
      dsimp [vn, Affine.negY, WeierstrassCurve.map]
      simp only [map_neg, map_sub, Derivation.leibniz, Derivation.map_algebraMap,
        smul_eq_mul, sub_zero]
      rw [hu, hv]
      ring
    obtain ⟨a, b, ha, hb⟩ := opposite_velocity_sum_constant E E' hP.1 hqn.1 hxu
      (r := 1) (by simpa using hx) (by simpa using hy) hun hvn
    have hn := Affine.nonsingular_add hP hqn (fun h => hxu h.1)
    rw [Affine.slope_of_X_ne hxu] at hn
    have hn' := hn
    rw [ha, hb] at hn'
    refine ⟨a, b, (Affine.map_nonsingular E'.toAffine
      (algebraMap K (FunctionField E)).injective a b).mp hn', ?_⟩
    rw [sub_eq_add_neg, Affine.Point.neg_some, Affine.Point.add_of_X_ne hxu]
    simp only [Affine.slope_of_X_ne hxu]
    congr 1
end WeierstrassCurve.Velu
namespace WeierstrassCurve.Velu
open RatFunc
open scoped WeierstrassCurve.Affine
variable {K : Type*} [Field K] [CharZero K] [DecidableEq K]
variable (E : WeierstrassCurve K) (G : AddSubgroup E.toAffine.Point) [Fintype G]

/-- The generic Vélu coordinates form a nonsingular point. -/
theorem velu_lift_nonsingular (hodd : ∀ Q : G, Q ≠ 0 → Q ≠ -Q) :
    ((curve E G).map (algebraMap K (FunctionField E))).toAffine.Nonsingular
      (liftX E (xFunction E G))
      (liftY E (curve E G) (xFunction E G) (slopeFunction E G)) := by
  rw [Affine.nonsingular_iff']
  exact ⟨velu_lift_equation E G hodd,
    Or.inr (lift_completedY_ne_zero E (curve E G) _ _ (slopeFunction_ne_zero E G))⟩

/-- The translated Vélu coordinates form a nonsingular point. -/
theorem translated_image_nonsingular [E.IsElliptic]
    (hodd : ∀ Q : G, Q ≠ 0 → Q ≠ -Q) {u v : K} (hQ : E.toAffine.Nonsingular u v) :
    ((curve E G).map (algebraMap K (FunctionField E))).toAffine.Nonsingular
      (imageX E G (substitution _ (translateX_transcendental E hQ)))
      (imageY E G (substitution _ (translateX_transcendental E hQ)) (translateY E u v)) := by
  rw [Affine.nonsingular_iff']
  refine ⟨translated_image_equation E G hodd hQ, Or.inr ?_⟩
  apply image_completedY_ne_zero
  simpa using translate_completedY_ne_zero E hQ

open Classical in
/-- The translation defect of the generic Vélu coordinates is a base-field point. -/
theorem translated_image_difference_constant [E.IsElliptic]
    (hodd : ∀ Q : G, Q ≠ 0 → Q ≠ -Q) {u v : K} (hQ : E.toAffine.Nonsingular u v) :
    let P := Affine.Point.some
      (imageX E G (substitution _ (translateX_transcendental E hQ)))
      (imageY E G (substitution _ (translateX_transcendental E hQ)) (translateY E u v))
      (translated_image_nonsingular E G hodd hQ)
    let R := Affine.Point.some (liftX E (xFunction E G))
      (liftY E (curve E G) (xFunction E G) (slopeFunction E G))
      (velu_lift_nonsingular E G hodd)
    P = R ∨ ∃ (a b : K) (h : (curve E G).toAffine.Nonsingular a b),
      P - R = Affine.Point.some (algebraMap K _ a) (algebraMap K _ b)
        ((Affine.map_nonsingular (curve E G).toAffine
          (algebraMap K (FunctionField E)).injective a b).mpr h) := by
  exact equal_velocity_difference_constant E (curve E G)
    (translated_image_nonsingular E G hodd hQ) (velu_lift_nonsingular E G hodd)
    (translated_image_derivation_x E G hQ) (translated_image_derivation_y E G hodd hQ)
    (velu_lift_derivation_x E G) (velu_lift_derivation_y E G hodd)
end WeierstrassCurve.Velu
