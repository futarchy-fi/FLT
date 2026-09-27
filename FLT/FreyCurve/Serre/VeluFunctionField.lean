/-
Copyright (c) 2026 krandder. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: krandder
-/
module

public import FLT.FreyCurve.Serre.VeluElliptic
public import Mathlib.Algebra.QuadraticAlgebra.Basic
/-!
# The invariant derivation in Vélu's construction

The quadratic model K(X)[ω], with ω² equal to the two-torsion cubic, is a field.
Its invariant derivation sends X to ω and has exactly K as its field of constants.

The lifted Vélu coordinates satisfy the target equation and preserve this
derivation. The differential addition formula shows that two moving points with
opposite velocities have constant sum, when their x-coordinates differ.

These results do not yet prove additivity of the Vélu map: translation of the
generic source point and determination of the resulting constant remain to be
connected to the explicit coordinate sums.
-/

@[expose] public section

namespace WeierstrassCurve.Affine
variable {K L : Type*} [Field K] [Field L] [Algebra K L]

/-- The curve equation determines the y-velocity from the x-velocity away from two-torsion. -/
theorem derivation_y_of_equation (E : WeierstrassCurve K) (d : Derivation K L L)
    {x y v : L}
    (heq : (E.map (algebraMap K L)).toAffine.Equation x y)
    (hx : d x = v * (2 * y + algebraMap K L E.a₁ * x + algebraMap K L E.a₃))
    (hy : 2 * y + algebraMap K L E.a₁ * x + algebraMap K L E.a₃ ≠ 0) :
    d y = v * (3 * x ^ 2 + 2 * algebraMap K L E.a₂ * x + algebraMap K L E.a₄ -
      algebraMap K L E.a₁ * y) := by
  have h := congrArg d ((equation_iff _ _).mp heq)
  simp only [WeierstrassCurve.map, map_add, Derivation.leibniz,
    Derivation.leibniz_pow, Derivation.map_algebraMap, smul_eq_mul] at h
  rw [hx] at h
  apply mul_left_cancel₀ hy
  linear_combination h

set_option maxRecDepth 4096 in
set_option maxHeartbeats 800000 in
-- The chord identity expands two cubic equations after clearing denominators.
/-- Invariant velocities add under the chord formula. -/
theorem derivation_addX (E : WeierstrassCurve K) (d : Derivation K L L)
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
    d ((E.map (algebraMap K L)).toAffine.addX x u ((y - v) / (x - u))) =
      (r + s) * (2 * (E.map (algebraMap K L)).toAffine.addY x u y ((y - v) / (x - u)) +
        algebraMap K L E.a₁ * 
          (E.map (algebraMap K L)).toAffine.addX x u ((y - v) / (x - u)) +
        algebraMap K L E.a₃) := by
  have hp := (equation_iff _ _).mp hP
  have hq := (equation_iff _ _).mp hQ
  dsimp [WeierstrassCurve.map] at hp hq
  have hl : d ((y - v) / (x - u)) =
      ((x - u) * (d y - d v) - (y - v) * (d x - d u)) / (x - u) ^ 2 := by
    rw [d.leibniz_div]
    simp only [map_sub, smul_eq_mul, div_eq_mul_inv, inv_pow]
    ring
  have hdx : d ((E.map (algebraMap K L)).toAffine.addX x u ((y - v) / (x - u))) =
      (2 * ((y - v) / (x - u)) + algebraMap K L E.a₁) * d ((y - v) / (x - u)) - d x - d u := by
    simp only [addX, WeierstrassCurve.map, map_sub, map_add,
      Derivation.leibniz, Derivation.leibniz_pow, Derivation.map_algebraMap, smul_eq_mul]
    ring
  rw [hdx, hl, hx, hy, hu, hv]
  simp only [addX, addY, negAddY, negY, WeierstrassCurve.map]
  field_simp [sub_ne_zero.mpr hxu]
  linear_combination
    -(r - s) * (algebraMap K L E.a₁ * (x - u) + 2 * (y - v)) * hp +
    (r - s) * (algebraMap K L E.a₁ * (x - u) + 2 * (y - v)) * hq

/-- On the curve, a constant x-coordinate forces a constant y-coordinate. -/
theorem derivation_y_eq_zero_of_x_eq_zero [NeZero (2 : L)]
    (E : WeierstrassCurve K) (d : Derivation K L L) {x y : L}
    (heq : (E.map (algebraMap K L)).toAffine.Equation x y) (hx : d x = 0) :
    d y = 0 := by
  by_cases hs : 2 * y + algebraMap K L E.a₁ * x + algebraMap K L E.a₃ = 0
  · have h := congrArg d hs
    have hd2 : d (2 : L) = 0 := d.map_natCast 2
    simp only [map_add, Derivation.leibniz, hd2,
      Derivation.map_algebraMap, hx, map_zero, smul_eq_mul,
      mul_zero, add_zero] at h
    exact (mul_eq_zero.mp h).resolve_left (NeZero.ne (2 : L))
  · simpa using derivation_y_of_equation E d heq
      (v := 0) (by simpa using hx) hs
end WeierstrassCurve.Affine




open scoped Polynomial
namespace RatFunc
variable {K : Type*} [Field K] [CharZero K]

/-- The invariant derivation on the quadratic model, with D(X) = ω and D(ω) = F'/2. -/
noncomputable def quadraticDerivation (F : K⟮X⟯) :
    Derivation K (QuadraticAlgebra K⟮X⟯ F 0) (QuadraticAlgebra K⟮X⟯ F 0) where
  toFun z := ⟨F * formalDerivation z.im + formalDerivation F / 2 * z.im,
    formalDerivation z.re⟩
  map_add' z w := by
    ext <;> simp [map_add]; ring
  map_smul' c z := by
    apply QuadraticAlgebra.ext
    · change F * formalDerivation (c • z.im) + formalDerivation F / 2 * (c • z.im) =
        c • (F * formalDerivation z.im + formalDerivation F / 2 * z.im)
      simp only [smul_eq_C_mul, Derivation.leibniz, formalDerivation_C, smul_eq_mul,
        mul_zero, add_zero]
      ring
    · change formalDerivation (c • z.re) = c • formalDerivation z.re
      simp [smul_eq_C_mul, Derivation.leibniz]
  map_one_eq_zero' := by
    change (⟨F * formalDerivation 0 + formalDerivation F / 2 * 0,
      formalDerivation 1⟩ : QuadraticAlgebra K⟮X⟯ F 0) = 0
    ext <;> simp
  leibniz' z w := by
    ext <;> simp [Derivation.leibniz, map_add, smul_eq_mul] <;> ring

/-- For an odd-degree radicand, the invariant derivation has exactly the base constants. -/
theorem quadraticDerivation_eq_zero_iff (F : K⟮X⟯)
    (hF : F ≠ 0) (hdeg : Odd F.intDegree)
    (z : QuadraticAlgebra K⟮X⟯ F 0) :
    quadraticDerivation F z = 0 ↔ ∃ c : K, z = algebraMap K _ c := by
  constructor
  · intro hz
    have hre : formalDerivation z.re = 0 :=
      congrArg QuadraticAlgebra.im hz
    have him : F * formalDerivation z.im + formalDerivation F / 2 * z.im = 0 :=
      congrArg QuadraticAlgebra.re hz
    have hd : formalDerivation (F * z.im ^ 2) = 0 := by
      simp only [Derivation.leibniz, Derivation.leibniz_pow, smul_eq_mul]
      linear_combination 2 * z.im * him
    obtain ⟨c, hc⟩ := (formalDeriv_eq_zero_iff _).mp hd
    have hi : z.im = 0 := by
      by_contra hi
      have h := congrArg intDegree hc
      rw [intDegree_mul hF (pow_ne_zero _ hi), pow_two,
        intDegree_mul hi hi, intDegree_C] at h
      rcases hdeg with ⟨m, hm⟩
      omega
    obtain ⟨a, ha⟩ := (formalDeriv_eq_zero_iff _).mp hre
    refine ⟨a, ?_⟩
    apply QuadraticAlgebra.ext
    · exact ha
    · exact hi
  · rintro ⟨c, rfl⟩
    exact (quadraticDerivation F).map_algebraMap c


omit [CharZero K] in
/-- A nonzero rational function of odd degree is not a square. -/
theorem not_isSquare_of_odd_intDegree (F : K⟮X⟯) (hF : F ≠ 0)
    (hdeg : Odd F.intDegree) : ¬IsSquare F := by
  rintro ⟨f, hf⟩
  have hf0 : f ≠ 0 := by
    intro h
    exact hF (by simpa only [h, mul_zero] using hf)
  have hd := congrArg intDegree hf
  rw [intDegree_mul hf0 hf0] at hd
  rcases hdeg with ⟨m, hm⟩
  omega

/-- On rational functions, the invariant derivation is ω times the formal derivative. -/
theorem quadraticDerivation_algebraMap (F f : K⟮X⟯) :
    quadraticDerivation F (algebraMap K⟮X⟯ _ f) =
      algebraMap K⟮X⟯ _ (formalDerivation f) * 
        (QuadraticAlgebra.omega : QuadraticAlgebra K⟮X⟯ F 0) := by
  ext <;> simp [quadraticDerivation, QuadraticAlgebra.algebraMap_eq,
    QuadraticAlgebra.omega]

/-- The invariant derivative of the quadratic generator is F'/2. -/
theorem quadraticDerivation_omega (F : K⟮X⟯) :
    quadraticDerivation F (QuadraticAlgebra.omega : QuadraticAlgebra K⟮X⟯ F 0) =
      algebraMap K⟮X⟯ _ (formalDerivation F / 2) := by
  ext <;> simp [quadraticDerivation, QuadraticAlgebra.algebraMap_eq,
    QuadraticAlgebra.omega]
end RatFunc

namespace WeierstrassCurve.Velu
open RatFunc
variable {K : Type*} [Field K] [CharZero K]

/-- The two-torsion cubic viewed as a rational function. -/
noncomputable def cubicFunction (E : WeierstrassCurve K) : K⟮X⟯ :=
  algebraMap K[X] K⟮X⟯ E.twoTorsionPolynomial.toPoly

omit [CharZero K] in
/-- The explicit expression for the rational two-torsion cubic. -/
theorem cubicFunction_eq (E : WeierstrassCurve K) :
    cubicFunction E = 4 * X ^ 3 + C E.b₂ * X ^ 2 + 2 * C E.b₄ * X + C E.b₆ := by
  simp [cubicFunction, twoTorsionPolynomial, Cubic.toPoly, map_ofNat]

/-- The two-torsion cubic has degree three. -/
theorem intDegree_cubicFunction (E : WeierstrassCurve K) :
    (cubicFunction E).intDegree = 3 := by
  rw [cubicFunction, intDegree_polynomial]
  have h := Cubic.degree_of_a_ne_zero (P := E.twoTorsionPolynomial)
    (by norm_num [twoTorsionPolynomial])
  rw [Polynomial.natDegree_eq_of_degree_eq_some h]
  rfl

/-- The two-torsion cubic is nonzero. -/
theorem cubicFunction_ne_zero (E : WeierstrassCurve K) : cubicFunction E ≠ 0 := by
  intro h
  have hd := intDegree_cubicFunction E
  rw [h, intDegree_zero] at hd
  norm_num at hd

/-- A quadratic model of the curve's function field using the completed y-coordinate. -/
noncomputable abbrev FunctionField (E : WeierstrassCurve K) :=
  QuadraticAlgebra K⟮X⟯ (cubicFunction E) 0

/-- The canonical coefficient inclusion,
chosen explicitly over RatFunc's lifted algebra instance. -/
noncomputable instance functionFieldRatAlgebra (E : WeierstrassCurve K) :
    Algebra K⟮X⟯ (FunctionField E) := QuadraticAlgebra.instAlgebra

instance (E : WeierstrassCurve K) : Fact (¬IsSquare (cubicFunction E)) :=
  ⟨not_isSquare_of_odd_intDegree _ (cubicFunction_ne_zero E)
    (by rw [intDegree_cubicFunction]; decide)⟩


/-- The invariant derivation of the quadratic curve model has only base-field constants. -/
theorem functionField_derivation_eq_zero_iff (E : WeierstrassCurve K)
    (z : FunctionField E) :
    quadraticDerivation (cubicFunction E) z = 0 ↔ ∃ c : K, z = algebraMap K _ c :=
  quadraticDerivation_eq_zero_iff _ (cubicFunction_ne_zero E)
    (by rw [intDegree_cubicFunction]; decide) z


omit [CharZero K] in
/-- A base-field coefficient has the expected rational real component. -/
@[simp] theorem functionField_algebraMap_re (E : WeierstrassCurve K) (c : K) :
    (algebraMap K (FunctionField E) c).re = C c := rfl

omit [CharZero K] in
/-- A base-field coefficient has zero quadratic component. -/
@[simp] theorem functionField_algebraMap_im (E : WeierstrassCurve K) (c : K) :
    (algebraMap K (FunctionField E) c).im = 0 := rfl


omit [CharZero K] in
/-- The canonical rational coefficient inclusion preserves the real component. -/
@[simp] theorem functionField_rat_re (E : WeierstrassCurve K) (f : K⟮X⟯) :
    (algebraMap K⟮X⟯ (FunctionField E) f).re = f := rfl

omit [CharZero K] in
/-- The canonical rational coefficient inclusion has zero quadratic component. -/
@[simp] theorem functionField_rat_im (E : WeierstrassCurve K) (f : K⟮X⟯) :
    (algebraMap K⟮X⟯ (FunctionField E) f).im = 0 := rfl

/-- The real component of two is two. -/
@[simp] theorem functionField_two_re (E : WeierstrassCurve K) :
    (2 : FunctionField E).re = 2 := rfl

/-- The quadratic component of two vanishes. -/
@[simp] theorem functionField_two_im (E : WeierstrassCurve K) :
    (2 : FunctionField E).im = 0 := rfl

/-- The x-coordinate in the quadratic model. -/
noncomputable def liftX (E : WeierstrassCurve K) (f : K⟮X⟯) : FunctionField E :=
  algebraMap K⟮X⟯ _ f

/-- The y-coordinate recovered from its completed form gω. -/
noncomputable def liftY (E E' : WeierstrassCurve K) (f g : K⟮X⟯) : FunctionField E :=
  ⟨(-C E'.a₁ * f - C E'.a₃) / 2, g / 2⟩

/-- A rational cubic identity gives an actual affine equation in the quadratic model. -/
theorem lift_equation (E E' : WeierstrassCurve K) (f g : K⟮X⟯)
    (heq : cubicFunction E * g ^ 2 =
      4 * f ^ 3 + C E'.b₂ * f ^ 2 + 2 * C E'.b₄ * f + C E'.b₆) :
    (E'.map (algebraMap K (FunctionField E))).toAffine.Equation
      (liftX E f) (liftY E E' f g) := by
  rw [Affine.equation_iff]
  apply QuadraticAlgebra.ext
  all_goals
    simp [ liftX, liftY, WeierstrassCurve.map, pow_succ
]
  · simp only [b₂, b₄, b₆, map_add, map_mul, map_pow, map_ofNat] at heq
    linear_combination heq / 4
  · ring

/-- The derivative of a lifted x-coordinate is its completed y-coordinate. -/
theorem derivation_liftX (E E' : WeierstrassCurve K) (f : K⟮X⟯) :
    quadraticDerivation (cubicFunction E) (liftX E f) =
      2 * liftY E E' f (formalDerivation f) +
        algebraMap K _ E'.a₁ * liftX E f + algebraMap K _ E'.a₃ := by
  apply QuadraticAlgebra.ext
  all_goals
    simp [ quadraticDerivation, liftX, liftY, QuadraticAlgebra.algebraMap_eq]
    ring

/-- The normalized Vélu slope is nonzero since its x-coordinate is nonconstant. -/
theorem slopeFunction_ne_zero [DecidableEq K] (E : WeierstrassCurve K)
    (G : AddSubgroup E.toAffine.Point) [Fintype G] : slopeFunction E G ≠ 0 := by
  intro h
  have hd : formalDeriv (xFunction E G) = 0 := (derivation_xFunction E G).trans h
  obtain ⟨c, hc⟩ := (formalDeriv_eq_zero_iff _).mp hd
  apply xFunction_sub_C_not_degreeLE E G c
  simp [hc, DegreeLE]


/-- The lifted Vélu coordinates satisfy the candidate curve equation. -/
theorem velu_lift_equation [DecidableEq K] (E : WeierstrassCurve K)
    (G : AddSubgroup E.toAffine.Point) [Fintype G]
    (hodd : ∀ Q : G, Q ≠ 0 → Q ≠ -Q) :
    ((curve E G).map (algebraMap K (FunctionField E))).toAffine.Equation
      (liftX E (xFunction E G)) (liftY E (curve E G) (xFunction E G) (slopeFunction E G)) := by
  apply lift_equation
  rw [cubicFunction_eq]
  convert rational_equation_coefficients E G hodd using 1
  simp only [curve, b₂, b₄, b₆, map_add, map_sub, map_mul, map_pow, map_ofNat]
  ring

/-- Vélu's generic x-coordinate preserves the invariant derivation. -/
theorem velu_lift_derivation_x [DecidableEq K] (E : WeierstrassCurve K)
    (G : AddSubgroup E.toAffine.Point) [Fintype G] :
    quadraticDerivation (cubicFunction E) (liftX E (xFunction E G)) =
      2 * liftY E (curve E G) (xFunction E G) (slopeFunction E G) +
        algebraMap K _ (curve E G).a₁ * liftX E (xFunction E G) +
        algebraMap K _ (curve E G).a₃ := by
  rw [← derivation_xFunction E G]
  exact derivation_liftX E (curve E G) (xFunction E G)

/-- A nonzero slope gives a nonzero completed y-coordinate in the quadratic model. -/
theorem lift_completedY_ne_zero (E E' : WeierstrassCurve K) (f g : K⟮X⟯)
    (hg : g ≠ 0) :
    2 * liftY E E' f g + algebraMap K _ E'.a₁ * liftX E f +
      algebraMap K _ E'.a₃ ≠ 0 := by
  intro h
  have hh := congrArg QuadraticAlgebra.im h
  exact hg (by simpa [liftY, liftX] using hh)

end WeierstrassCurve.Velu




namespace WeierstrassCurve.Velu
open RatFunc
variable {K : Type*} [Field K] [CharZero K]

/-- Vélu's generic y-coordinate preserves the invariant derivation. -/
theorem velu_lift_derivation_y [DecidableEq K] (E : WeierstrassCurve K)
    (G : AddSubgroup E.toAffine.Point) [Fintype G]
    (hodd : ∀ Q : G, Q ≠ 0 → Q ≠ -Q) :
    quadraticDerivation (cubicFunction E)
        (liftY E (curve E G) (xFunction E G) (slopeFunction E G)) =
      3 * liftX E (xFunction E G) ^ 2 +
        2 * algebraMap K _ (curve E G).a₂ * liftX E (xFunction E G) +
        algebraMap K _ (curve E G).a₄ -
        algebraMap K _ (curve E G).a₁ * 
          liftY E (curve E G) (xFunction E G) (slopeFunction E G) := by
  simpa using Affine.derivation_y_of_equation (curve E G)
    (quadraticDerivation (cubicFunction E)) (velu_lift_equation E G hodd)
    (v := 1) (by simpa using velu_lift_derivation_x E G)
    (lift_completedY_ne_zero E (curve E G) _ _ (slopeFunction_ne_zero E G))

/-- Two points with opposite invariant velocities have constant sum in the chord case. -/
theorem opposite_velocity_sum_constant (E E' : WeierstrassCurve K)
    {x y u v r : FunctionField E}
    (hP : (E'.map (algebraMap K (FunctionField E))).toAffine.Equation x y)
    (hQ : (E'.map (algebraMap K (FunctionField E))).toAffine.Equation u v)
    (hxu : x ≠ u)
    (hx : quadraticDerivation (cubicFunction E) x =
      r * (2 * y + algebraMap K _ E'.a₁ * x + algebraMap K _ E'.a₃))
    (hy : quadraticDerivation (cubicFunction E) y =
      r * (3 * x ^ 2 + 2 * algebraMap K _ E'.a₂ * x + algebraMap K _ E'.a₄ -
        algebraMap K _ E'.a₁ * y))
    (hu : quadraticDerivation (cubicFunction E) u =
      -r * (2 * v + algebraMap K _ E'.a₁ * u + algebraMap K _ E'.a₃))
    (hv : quadraticDerivation (cubicFunction E) v =
      -r * (3 * u ^ 2 + 2 * algebraMap K _ E'.a₂ * u + algebraMap K _ E'.a₄ -
        algebraMap K _ E'.a₁ * v)) :
    ∃ a b : K,
      (E'.map (algebraMap K (FunctionField E))).toAffine.addX x u ((y - v) / (x - u)) =
        algebraMap K _ a ∧
      (E'.map (algebraMap K (FunctionField E))).toAffine.addY x u y ((y - v) / (x - u)) =
        algebraMap K _ b := by
  classical
  have hdx := Affine.derivation_addX E' (quadraticDerivation (cubicFunction E))
    hP hQ hxu hx hy hu hv
  simp only [add_neg_cancel, zero_mul] at hdx
  have heq := Affine.equation_add hP hQ (fun h => hxu h.1)
  rw [Affine.slope_of_X_ne hxu] at heq
  have hdy := Affine.derivation_y_eq_zero_of_x_eq_zero E'
    (quadraticDerivation (cubicFunction E)) heq hdx
  obtain ⟨a, ha⟩ := (functionField_derivation_eq_zero_iff E _).mp hdx
  obtain ⟨b, hb⟩ := (functionField_derivation_eq_zero_iff E _).mp hdy
  exact ⟨a, b, ha, hb⟩
end WeierstrassCurve.Velu
