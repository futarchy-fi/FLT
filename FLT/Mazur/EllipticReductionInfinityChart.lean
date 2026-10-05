/-
Copyright (c) 2026 krandder. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: krandder
-/
module

public import FLT.Mazur.EllipticSmoothReduction

/-!
# The integral chart at the reduction of infinity

The infinity fiber is characterized by the vanishing of the reduced homogeneous
Z coordinate. Its Y coordinate is a unit. The parameters `t = -X/Y` and `s = -Z/Y`
are in the maximal ideal and satisfy the integral Weierstrass equation at infinity.
This supplies coordinates, not a multiplication series or a torsion bound.
-/

@[expose] public section

namespace FLT.Mazur

open IsLocalRing WeierstrassCurve WeierstrassCurve.Projective

variable {K : Type*} [Field K] (A : ValuationSubring K) (W : WeierstrassCurve A)
  {P : (W.map (algebraMap A K)).toProjective.Point}

/-- A primitive reduced point on the line at infinity has nonzero Y coordinate. -/
theorem PrimitiveLift.residue_y_ne_zero (v : PrimitiveLift A P.point)
    (hz : residue A (v.coords 2) = 0) : residue A (v.coords 1) ≠ 0 := by
  have hx : residue A (v.coords 0) = 0 :=
    X_eq_zero_of_Z_eq_zero (v.residue_equation A W) hz
  obtain ⟨i, hi⟩ := v.residue_ne_zero A
  intro hy
  fin_cases i
  · exact hi hx
  · exact hi hy
  · exact hi hz

/-- The infinity fiber is exactly the vanishing of the reduced Z coordinate. -/
theorem infinityReduction_iff_residue_z (v : PrimitiveLift A P.point) :
    InfinityReduction A W P ↔ residue A (v.coords 2) = 0 := by
  change projectiveReduction A W P = _ ↔ _
  rw [projectiveReduction_eq A W P v]
  constructor
  · intro h
    exact (Z_eq_zero_of_equiv (Quotient.exact h)).mpr rfl
  · intro hz
    apply Quotient.sound
    have hx : residue A (v.coords 0) = 0 :=
      X_eq_zero_of_Z_eq_zero (v.residue_equation A W) hz
    have he : residue A ∘ v.coords = residue A (v.coords 1) • ![0, 1, 0] := by
      ext i
      fin_cases i <;> simp [Function.comp_apply, hx, hz]
    rw [he]
    exact smul_equiv _ (Ne.isUnit (v.residue_y_ne_zero A W hz))

/-- In the infinity fiber, the homogeneous Y coordinate is an integral unit. -/
theorem PrimitiveLift.isUnit_y (v : PrimitiveLift A P.point)
    (h : InfinityReduction A W P) : IsUnit (v.coords 1) :=
  (residue_ne_zero_iff_isUnit _).mp
    (v.residue_y_ne_zero A W ((infinityReduction_iff_residue_z A W v).mp h))

/-- An affine point reduces to infinity exactly when its coordinates are not both integral. -/
theorem infinityReduction_affine_iff {x y : K}
    (h : (W.map (algebraMap A K)).toAffine.Nonsingular x y) :
    InfinityReduction A W (Affine.Point.toProjective (.some _ _ h)) ↔
      ¬ (x ∈ A ∧ y ∈ A) := by
  classical
  constructor
  · intro hinf hi
    exact not_infinityReduction_affine A W ⟨x, hi.1⟩ ⟨y, hi.2⟩ h hinf
  · intro hi
    let P := Affine.Point.toProjective (.some _ _ h)
    let v := primitiveLift A W P
    apply (infinityReduction_iff_residue_z A W v).mpr
    by_contra hz
    have hu : IsUnit (v.coords 2) := (residue_ne_zero_iff_isUnit _).mp hz
    have he : (fun i => (v.coords i : K)) ≈ ![x, y, 1] :=
      Quotient.exact v.represents
    have hx : (v.coords 0 : K) = x * (v.coords 2 : K) := by
      simpa using X_eq_of_equiv he
    have hy : (v.coords 1 : K) = y * (v.coords 2 : K) := by
      simpa using Y_eq_of_equiv he
    have hm (i : Fin 3) (u : K) (hh : (v.coords i : K) = u * (v.coords 2 : K)) :
        u ∈ A :=
      scalar_mem_of_primitive A (v := fun _ : Unit => v.coords i)
        (w := fun _ : Unit => v.coords 2) ⟨(), hu⟩ (fun _ => hh)
    exact hi ⟨hm 0 x hx, hm 1 y hy⟩

/-- Nonintegral affine points always reduce to a smooth point, namely infinity. -/
theorem smoothReduction_of_nonintegral {x y : K}
    (h : (W.map (algebraMap A K)).toAffine.Nonsingular x y)
    (hi : ¬ (x ∈ A ∧ y ∈ A)) :
    SmoothReduction A W (Affine.Point.toProjective (.some _ _ h)) :=
  ((infinityReduction_affine_iff A W h).mpr hi).smooth A W

/-- The formal coordinates at infinity lie in the maximal ideal and satisfy the local equation. -/
theorem exists_infinity_parameters (v : PrimitiveLift A P.point)
    (h : InfinityReduction A W P) :
    ∃ t s : A, (t : K) = -(v.coords 0 : K) / (v.coords 1 : K) ∧
      (s : K) = -(v.coords 2 : K) / (v.coords 1 : K) ∧
      t ∈ maximalIdeal A ∧ s ∈ maximalIdeal A ∧
      s = t ^ 3 + W.a₁ * t * s + W.a₂ * t ^ 2 * s + W.a₃ * s ^ 2 +
        W.a₄ * t * s ^ 2 + W.a₆ * s ^ 3 := by
  have hu := v.isUnit_y A W h
  let d : A := ↑hu.unit⁻¹
  let t : A := -v.coords 0 * d
  let s : A := -v.coords 2 * d
  have hd : (d : K) = (v.coords 1 : K)⁻¹ :=
    map_units_inv (algebraMap A K) hu.unit
  have ht : (t : K) = -(v.coords 0 : K) / (v.coords 1 : K) := by
    change -(v.coords 0 : K) * (d : K) = _
    rw [hd, div_eq_mul_inv]
  have hs : (s : K) = -(v.coords 2 : K) / (v.coords 1 : K) := by
    change -(v.coords 2 : K) * (d : K) = _
    rw [hd, div_eq_mul_inv]
  have hz := (infinityReduction_iff_residue_z A W v).mp h
  have hx : residue A (v.coords 0) = 0 :=
    X_eq_zero_of_Z_eq_zero (v.residue_equation A W) hz
  refine ⟨t, s, ht, hs, ?_, ?_, ?_⟩
  · rw [← residue_eq_zero_iff]
    simp only [t, map_mul, map_neg, hx, neg_zero, zero_mul]
  · rw [← residue_eq_zero_iff]
    simp only [s, map_mul, map_neg, hz, neg_zero, zero_mul]
  · apply IsFractionRing.injective A K
    simp only [map_add, map_mul, map_pow, ValuationSubring.algebraMap_apply, ht, hs]
    have hy0 : (v.coords 1 : K) ≠ 0 := fun hh => hu.ne_zero (Subtype.ext hh)
    have he := (equation_iff _).mp ((v.equation A W).map (algebraMap A K))
    simp only [Function.comp_apply, map_a₁, map_a₂, map_a₃, map_a₄, map_a₆,
      ValuationSubring.algebraMap_apply] at he
    field_simp
    linear_combination -he

end FLT.Mazur
