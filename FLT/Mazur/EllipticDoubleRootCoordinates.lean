/-
Copyright (c) 2026 krandder. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: krandder
-/
module

public import FLT.Mazur.EllipticStarZeroCoordinates
public import FLT.Mazur.RepeatedCubicRoots

/-!
# Coordinates over the double root in the additive branch

At depths (1,1,2,3,4), the residual cubic is T²(T + a₂/π).
Its zero label admits coordinates (π²x,π²y); the other label is simple
when a₂ has exact depth one.
-/

@[expose] public section

namespace FLT.Mazur

open WeierstrassCurve IsLocalRing

variable {K : Type*} [Field K] {A : ValuationSubring K} {W : WeierstrassCurve A}
  {π : A} {P Q : (W.map (algebraMap A K)).toProjective.Point}

/-- The double-root chart has just the repeated zero label and the other cubic root. -/
theorem StarZeroCoordinates.doubleRoot_label
    (v : StarZeroCoordinates A W π P) (hπ : π ≠ 0) (hπm : π ∈ maximalIdeal A)
    (e2 e3 e4 e6 : A) (h1 : W.a₁ ∈ maximalIdeal A)
    (h2 : W.a₂ = π * e2) (h3 : W.a₃ = π ^ 2 * e3)
    (h4 : W.a₄ = π ^ 2 * e4) (h6 : W.a₆ = π ^ 3 * e6)
    (h4m : e4 ∈ maximalIdeal A) (h6m : e6 ∈ maximalIdeal A) :
    residue A v.x = 0 ∨ residue A v.x = -residue A e2 := by
  have hr := starZero_scaled_residue W hπ hπm v.x v.y e2 e3 e4 e6
    h1 h2 h3 h4 h6 v.equation
  simp only [(residue_eq_zero_iff _).mpr h4m, (residue_eq_zero_iff _).mpr h6m,
    zero_mul, add_zero] at hr
  have hf : residue A v.x ^ 2 * (residue A v.x + residue A e2) = 0 := by
    linear_combination hr
  rcases mul_eq_zero.mp hf with hx | hx
  · exact Or.inl ((pow_eq_zero_iff (by decide : 2 ≠ 0)).mp hx)
  · exact Or.inr (eq_neg_of_add_eq_zero_left hx)

/-- A point over the repeated zero root has both coordinates divisible by π². -/
theorem StarZeroCoordinates.exists_doubleRootCoordinates
    (v : StarZeroCoordinates A W π P) (hgen : maximalIdeal A = Ideal.span {π})
    (hx : residue A v.x = 0) : Nonempty (TypeIVCoordinates A W (π ^ 2) P) := by
  obtain ⟨a, ha⟩ := exists_node_coordinate_factor hgen 1
    (by simpa using (residue_eq_zero_iff _).mp hx)
  simp only [pow_one] at ha
  have he : π * v.x = π ^ 2 * a := by rw [ha]; ring
  have hn : (W.map (algebraMap A K)).toAffine.Nonsingular
      ((π ^ 2 * a : A) : K) ((π ^ 2 * v.y : A) : K) := by
    simpa only [he] using v.nonsingular
  refine ⟨⟨a, v.y, hn, v.represents.trans ?_⟩⟩
  apply congrArg Affine.Point.toProjective
  simp only [Affine.Point.some.injEq]
  exact ⟨congrArg Subtype.val he, True.intro⟩

/-- The nonzero label is simple, so all points over it have the same component. -/
theorem StarZeroCoordinates.component_eq_of_doubleRoot_other
    (v : StarZeroCoordinates A W π P) (w : StarZeroCoordinates A W π Q)
    (hπ : π ≠ 0) (hπm : π ∈ maximalIdeal A) (e1 e2 e3 e4 : A)
    (h1 : W.a₁ = π * e1) (h2 : W.a₂ = π * e2)
    (h3 : W.a₃ = π ^ 2 * e3) (h4 : W.a₄ = π ^ 2 * e4)
    (h6 : W.a₆ ∈ maximalIdeal A) (h2m : e2 ∉ maximalIdeal A)
    (h4m : e4 ∈ maximalIdeal A)
    (hv : residue A v.x = -residue A e2) (hw : residue A w.x = -residue A e2) :
    ellipticComponentHom A W P = ellipticComponentHom A W Q := by
  apply v.component_eq_of_same w hπ hπm e1 e2 e3 e4 h1 h2 h3 h4 h6
    (hv.trans hw.symm)
  rw [hv, (residue_eq_zero_iff _).mpr h4m]
  have he : 3 * (-residue A e2) ^ 2 + 2 * residue A e2 * -residue A e2 + 0 =
      residue A e2 ^ 2 := by ring
  rw [he]
  exact pow_ne_zero 2 (fun hz => h2m ((residue_eq_zero_iff _).mp hz))

end FLT.Mazur
