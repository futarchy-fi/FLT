/-
Copyright (c) 2026 krandder. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: krandder
-/
module

public import FLT.Mazur.NodeTangentExtension
public import FLT.Mazur.EllipticNodeTangentSwap

/-!
# Tangent conjugation is an actual integral tangent exchange

Shearing by the adjoined tangent root removes a₂. Conjugating this sheared
model is exactly the integral tangent-swap variable change, coefficient by
coefficient, rather than an assumed action on component labels.
-/

@[expose] public section

namespace FLT.Mazur

open WeierstrassCurve

variable {R : Type*} [CommRing R] (W : WeierstrassCurve R)

/-- The integral model obtained by shearing along the distinguished tangent. -/
noncomputable def nodeTangentShear : WeierstrassCurve (AdjoinRoot (nodeTangentPolynomial W)) :=
  (⟨1, 0, AdjoinRoot.root (nodeTangentPolynomial W), 0⟩ : VariableChange _) •
    W.map (algebraMap R _)

/-- The tangent shear removes a₂ exactly and keeps a₃ and a₆ unchanged. -/
theorem nodeTangentShear_coefficients :
    (nodeTangentShear W).a₁ =
        algebraMap R _ W.a₁ + 2 * AdjoinRoot.root (nodeTangentPolynomial W) ∧
      (nodeTangentShear W).a₂ = 0 ∧
      (nodeTangentShear W).a₃ = algebraMap R _ W.a₃ ∧
      (nodeTangentShear W).a₄ = algebraMap R _ W.a₄ -
        AdjoinRoot.root (nodeTangentPolynomial W) * algebraMap R _ W.a₃ ∧
      (nodeTangentShear W).a₆ = algebraMap R _ W.a₆ := by
  simp only [nodeTangentShear, variableChange_a₁, variableChange_a₂, variableChange_a₃,
    variableChange_a₄, variableChange_a₆, map_a₁, map_a₂, map_a₃, map_a₄, map_a₆,
    inv_one, Units.val_one, one_pow, one_mul, zero_mul, mul_zero, add_zero,
    zero_pow (by decide : 2 ≠ 0), zero_pow (by decide : 3 ≠ 0), sub_zero]
  constructor
  · trivial
  constructor
  · linear_combination -nodeTangentRoot_equation W
  · exact ⟨trivial, trivial, trivial⟩

/-- The split model has unit a₁ when the original tangent discriminant is a unit. -/
theorem nodeTangentShear_a₁_isUnit (hb : IsUnit W.b₂) : IsUnit (nodeTangentShear W).a₁ := by
  rw [(nodeTangentShear_coefficients W).1]
  exact nodeTangentRoot_derivative_isUnit W hb

/-- Conjugating the split integral equation is the actual tangent-swap shear. -/
theorem nodeTangentShear_conjugate :
    (nodeTangentShear W).map (nodeTangentConjugation W).toRingHom =
      nodeTangentSwap (nodeTangentShear W) • nodeTangentShear W := by
  obtain ⟨h₁, h₂, h₃, h₄, h₆⟩ := nodeTangentShear_coefficients W
  obtain ⟨g₁, g₂, g₃, g₄, g₆⟩ := nodeTangentSwap_coefficients (nodeTangentShear W)
  have hc (r : R) : (nodeTangentConjugation W).toRingHom (algebraMap R _ r) =
      algebraMap R _ r := (nodeTangentConjugation W).commutes r
  have hr : (nodeTangentConjugation W).toRingHom (AdjoinRoot.root (nodeTangentPolynomial W)) =
      -algebraMap R _ W.a₁ - AdjoinRoot.root (nodeTangentPolynomial W) :=
    nodeTangentConjugationHom_root W
  ext <;> simp only [map_a₁, map_a₂, map_a₃, map_a₄, map_a₆,
    g₁, g₂, g₃, g₄, g₆, h₁, h₂, h₃, h₄, h₆, map_add, map_sub, map_mul,
    map_ofNat, map_zero, hc, hr] <;> ring

end FLT.Mazur
