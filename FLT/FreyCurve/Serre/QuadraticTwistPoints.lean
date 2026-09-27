/-
Copyright (c) 2026 krandder. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: krandder
-/
module

public import FLT.FreyCurve.Serre.MultiplicativeReduction

/-!
# The Galois sign of an explicit quadratic twist

The point comparison determined by a quadratic root intertwines an automorphism
with sign determined by whether that automorphism fixes or exchanges the root.
-/

@[expose] public section

open scoped WeierstrassCurve.Affine

namespace WeierstrassCurve

universe v
variable {K Ω : Type v} [Field K] [Field Ω] [Algebra K Ω] [DecidableEq Ω]
variable (E : WeierstrassCurve K) (t n : K) [(E.quadraticTwistOf t n).IsElliptic]
variable (x : Ω) (hx : x ^ 2 - algebraMap K Ω t * x + algebraMap K Ω n = 0)
variable (hw : algebraMap K Ω t - 2 * x ≠ 0)

/-- The change of variables attached to a root of the twisting quadratic. -/
noncomputable def quadraticRootChange : VariableChange Ω :=
  ⟨Units.mk0 (algebraMap K Ω t - 2 * x) hw, 0, -(x * (E.baseChange Ω).a₁),
    -((algebraMap K Ω t - 2 * x) ^ 2 * x * (E.baseChange Ω).a₃)⟩

omit [DecidableEq Ω] [(E.quadraticTwistOf t n).IsElliptic] in
include hx in
/-- The root change of variables identifies the twist with the original equation. -/
theorem quadraticRootChange_smul :
    E.quadraticRootChange t x hw • (E.quadraticTwistOf t n).baseChange Ω = E.baseChange Ω := by
  rw [baseChange, quadraticTwistOf_map]
  exact quadraticRoot_variableChange_smul _ _ _ _ hx hw

/-- A chosen quadratic root identifies points of the original curve and its twist. -/
noncomputable def quadraticRootPointEquiv :
    (E⁄Ω).Point ≃+ ((E.quadraticTwistOf t n)⁄Ω).Point :=
  (Affine.Point.equivOfEq (E.quadraticRootChange_smul t n x hx hw).symm).trans
    (Affine.Point.equivVariableChange ((E.quadraticTwistOf t n).baseChange Ω)
      (E.quadraticRootChange t x hw))

/-- Fixing the chosen quadratic root makes the point comparison equivariant. -/
theorem quadraticRootPointEquiv_fixed (σ : Ω ≃ₐ[K] Ω) (hσ : σ x = x)
    (P : (E⁄Ω).Point) :
    E.quadraticRootPointEquiv t n x hx hw (Affine.Point.map σ.toAlgHom P) =
      Affine.Point.map σ.toAlgHom (E.quadraticRootPointEquiv t n x hx hw P) := by
  rcases P with _ | ⟨a, b, h⟩
  · simp [quadraticRootPointEquiv, ← Affine.Point.zero_def]
  · simp only [quadraticRootPointEquiv, AddEquiv.trans_apply, Affine.Point.equivOfEq_some,
      Affine.Point.equivVariableChange_some, Affine.Point.map_some]
    apply Affine.Point.some_eq_some <;>
      simp [quadraticRootChange, hσ, AlgEquiv.commutes, baseChange, map_ofNat]

/-- Exchanging the quadratic roots changes Galois equivariance by negation. -/
theorem quadraticRootPointEquiv_conjugated (σ : Ω ≃ₐ[K] Ω)
    (hσ : σ x = algebraMap K Ω t - x) (P : (E⁄Ω).Point) :
    E.quadraticRootPointEquiv t n x hx hw (Affine.Point.map σ.toAlgHom P) =
      -Affine.Point.map σ.toAlgHom (E.quadraticRootPointEquiv t n x hx hw P) := by
  have hq : (algebraMap K Ω t - 2 * x) ^ 2 =
      (algebraMap K Ω t) ^ 2 - 4 * algebraMap K Ω n := by
    linear_combination 4 * hx
  rcases P with _ | ⟨a, b, h⟩
  · simp [quadraticRootPointEquiv, ← Affine.Point.zero_def]
  · simp only [quadraticRootPointEquiv, AddEquiv.trans_apply, Affine.Point.equivOfEq_some,
      Affine.Point.equivVariableChange_some, Affine.Point.map_some, Affine.Point.neg_some]
    apply Affine.Point.some_eq_some
    · simp only [AlgEquiv.coe_toAlgHom, quadraticRootChange, Units.val_mk0, map_add,
        map_mul, map_pow, map_sub, map_ofNat, map_zero, AlgEquiv.commutes, hσ]
      ring
    · simp only [AlgEquiv.coe_toAlgHom, quadraticRootChange, Units.val_mk0, map_add,
        map_mul, map_pow, map_sub, map_neg, map_ofNat, map_zero, AlgEquiv.commutes, hσ,
        Affine.negY]
      simp only [baseChange, quadraticTwistOf, map, map_mul, map_sub, map_pow,
        map_ofNat, AlgEquiv.commutes]
      change _ = -_ - (algebraMap K Ω t * _) * _ -
        ((algebraMap K Ω t) ^ 2 - 4 * algebraMap K Ω n) * algebraMap K Ω t * _
      rw [← hq]
      ring

/-- Fixing the discriminant square root gives the positive Galois sign. -/
theorem quadraticRootPointEquiv_discriminant_fixed (h2 : (2 : Ω) ≠ 0)
    (σ : Ω ≃ₐ[K] Ω)
    (hσ : σ (algebraMap K Ω t - 2 * x) = algebraMap K Ω t - 2 * x)
    (P : (E⁄Ω).Point) :
    E.quadraticRootPointEquiv t n x hx hw (Affine.Point.map σ.toAlgHom P) =
      Affine.Point.map σ.toAlgHom (E.quadraticRootPointEquiv t n x hx hw P) := by
  apply E.quadraticRootPointEquiv_fixed t n x hx hw σ _ P
  apply mul_left_cancel₀ h2
  simp only [map_sub, map_mul, map_ofNat, AlgEquiv.commutes] at hσ
  linear_combination -hσ

/-- Negating the discriminant square root gives the negative Galois sign. -/
theorem quadraticRootPointEquiv_discriminant_negated (h2 : (2 : Ω) ≠ 0)
    (σ : Ω ≃ₐ[K] Ω)
    (hσ : σ (algebraMap K Ω t - 2 * x) = -(algebraMap K Ω t - 2 * x))
    (P : (E⁄Ω).Point) :
    E.quadraticRootPointEquiv t n x hx hw (Affine.Point.map σ.toAlgHom P) =
      -Affine.Point.map σ.toAlgHom (E.quadraticRootPointEquiv t n x hx hw P) := by
  apply E.quadraticRootPointEquiv_conjugated t n x hx hw σ _ P
  apply mul_left_cancel₀ h2
  simp only [map_sub, map_mul, map_ofNat, AlgEquiv.commutes] at hσ
  linear_combination -hσ

end WeierstrassCurve
