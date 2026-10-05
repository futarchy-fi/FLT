/-
Copyright (c) 2026 krandder. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: krandder
-/
module

public import FLT.Mazur.NodeNonsplitTangent
public import Mathlib.Algebra.Polynomial.Degree.SmallDegree

/-!
# Fixed elements of the quadratic tangent field

The tangent field has basis 1,s. When b₂ is nonzero, its canonical
conjugation fixes exactly the ground field, including in characteristic two.
-/

@[expose] public section

namespace FLT.Mazur

open WeierstrassCurve Polynomial

variable {F : Type*} [Field F] (W : WeierstrassCurve F)
variable [Fact (Irreducible (nodeTangentPolynomial W))]

/-- Every element of the tangent field is linear in the distinguished root. -/
theorem nodeTangentField_exists_linear (z : AdjoinRoot (nodeTangentPolynomial W)) :
    ∃ b c : F, z = algebraMap F _ b * AdjoinRoot.root (nodeTangentPolynomial W) +
      algebraMap F _ c := by
  let pb := AdjoinRoot.powerBasis' (nodeTangentPolynomial_monic W)
  obtain ⟨f, hf, hz⟩ := pb.exists_eq_aeval z
  have hd : pb.dim = 2 := natDegree_eq_of_degree_eq_some (nodeTangentPolynomial_degree W)
  obtain ⟨b, c, hbc⟩ := exists_eq_X_add_C_of_natDegree_le_one (by omega : f.natDegree ≤ 1)
  refine ⟨b, c, ?_⟩
  rw [hz, hbc]
  simp [pb]

/-- The only elements fixed by tangent conjugation are the ground-field elements. -/
theorem nodeTangentField_fixed_iff (hb : W.b₂ ≠ 0)
    (z : AdjoinRoot (nodeTangentPolynomial W)) :
    nodeTangentConjugation W z = z ↔ ∃ c : F, algebraMap F _ c = z := by
  constructor
  · intro hz
    obtain ⟨b, c, rfl⟩ := nodeTangentField_exists_linear W z
    have hr : nodeTangentConjugation W (AdjoinRoot.root (nodeTangentPolynomial W)) =
        -algebraMap F _ W.a₁ - AdjoinRoot.root (nodeTangentPolynomial W) :=
      nodeTangentConjugationHom_root W
    rw [map_add, map_mul, AlgEquiv.commutes, AlgEquiv.commutes, hr] at hz
    have hu := nodeTangentRoot_derivative_isUnit W (isUnit_iff_ne_zero.mpr hb)
    have hzero : algebraMap F (AdjoinRoot (nodeTangentPolynomial W)) b = 0 := by
      apply (mul_eq_zero.mp (show algebraMap F _ b *
          (algebraMap F _ W.a₁ + 2 * AdjoinRoot.root (nodeTangentPolynomial W)) = 0 by
        linear_combination -hz)).resolve_right hu.ne_zero
    exact ⟨c, by rw [hzero, zero_mul, zero_add]⟩
  · rintro ⟨c, rfl⟩
    exact (nodeTangentConjugation W).commutes c

/-- The canonical conjugation sends the transverse tangent difference to its negative. -/
theorem nodeTangentField_conjugate_derivative :
    nodeTangentConjugation W
        (algebraMap F _ W.a₁ + 2 * AdjoinRoot.root (nodeTangentPolynomial W)) =
      -(algebraMap F _ W.a₁ + 2 * AdjoinRoot.root (nodeTangentPolynomial W)) := by
  have hr : nodeTangentConjugation W (AdjoinRoot.root (nodeTangentPolynomial W)) =
      -algebraMap F _ W.a₁ - AdjoinRoot.root (nodeTangentPolynomial W) :=
    nodeTangentConjugationHom_root W
  rw [map_add, map_mul, map_ofNat, AlgEquiv.commutes, hr]
  ring

end FLT.Mazur
