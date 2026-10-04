/-
Copyright (c) 2026 krandder. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: krandder
-/
module

public import FLT.GroupScheme.LocalIntegralScalars
public import FLT.GroupScheme.IntegralModelPoints

/-!
# Integral coefficient-unit automorphisms

The already constructed integral scalar maps give actual algebra automorphisms
for coefficient units. Their group law and Hopf compatibility come from the
original scalar maps, rather than being assumed as twist data.
-/

@[expose] public noncomputable section
open NumberField IsLocalRing
namespace ThreeAdicPlan

variable {K k : Type} [Field K] [NumberField K] [Field k]
  (v : IsDedekindDomain.HeightOneSpectrum (𝓞 K))
  [IsAdicComplete (maximalIdeal (v.adicCompletionIntegers K)) (v.adicCompletionIntegers K)]
  (p : ℕ) [Fact p.Prime] [CharP k p]
  [CharP (ResidueField (v.adicCompletionIntegers K)) p]
  (X : FF (v.adicCompletionIntegers K) (v.adicCompletion K)) [Module k X.Points]
  [SMulCommClass k (AlgebraicClosure (v.adicCompletion K) ≃ₐ[v.adicCompletion K]
    AlgebraicClosure (v.adicCompletion K)) X.Points]
  (he : RaynaudParameters.order (p : v.adicCompletionIntegers K) < p - 1)

/-- The specified integral scalar map preserves the identity scalar. -/
theorem localIntegralScalar_one : localIntegralScalar v p X he (1 : k) =
    BialgHom.id (v.adicCompletionIntegers K) X.CoordinateRing :=
  (exists_local_integral_scalars v p X he).choose_spec.2.2.1

/-- The specified scalar maps satisfy the contravariant multiplication law. -/
theorem localIntegralScalar_mul (a b : k) :
    localIntegralScalar v p X he (a * b) =
      (localIntegralScalar v p X he b).comp (localIntegralScalar v p X he a) :=
  (exists_local_integral_scalars v p X he).choose_spec.2.2.2.2 a b

/-- A coefficient unit gives an actual automorphism of the original integral coordinates. -/
def localIntegralUnitEquiv (a : kˣ) :
    X.CoordinateRing ≃ₐ[v.adicCompletionIntegers K] X.CoordinateRing :=
  AlgEquiv.ofAlgHom (localIntegralScalar v p X he (a : k)).toAlgHom
    (localIntegralScalar v p X he (↑a⁻¹ : k)).toAlgHom
    (by
      have h := localIntegralScalar_mul v p X he (↑a⁻¹ : k) (a : k)
      rw [Units.inv_mul, localIntegralScalar_one] at h
      exact (congrArg BialgHom.toAlgHom h).symm)
    (by
      have h := localIntegralScalar_mul v p X he (a : k) (↑a⁻¹ : k)
      rw [Units.mul_inv, localIntegralScalar_one] at h
      exact (congrArg BialgHom.toAlgHom h).symm)

/-- The coordinate automorphism group action of all coefficient units. -/
def localIntegralUnitAction : kˣ →*
    (X.CoordinateRing ≃ₐ[v.adicCompletionIntegers K] X.CoordinateRing) where
  toFun := localIntegralUnitEquiv v p X he
  map_one' := by
    apply AlgEquiv.coe_toAlgHom_injective
    exact congrArg BialgHom.toAlgHom (localIntegralScalar_one v p X he)
  map_mul' a b := by
    apply AlgEquiv.coe_toAlgHom_injective
    have h := localIntegralScalar_mul v p X he (b : k) (a : k)
    rw [mul_comm] at h
    exact congrArg BialgHom.toAlgHom h

/-- The automorphism is the already constructed Hopf-compatible scalar map. -/
theorem localIntegralUnitAction_toAlgHom (a : kˣ) :
    (localIntegralUnitAction v p X he a).toAlgHom =
      (localIntegralScalar v p X he (a : k)).toAlgHom := rfl

/-- Pullback of an actual integral point is the prescribed coefficient multiplication. -/
theorem localIntegralUnitAction_point (a : kˣ) (x : X.Points) :
    (X.integralPoints x).comp (localIntegralUnitAction v p X he a).toAlgHom =
      X.integralPoints ((a : k) • x) := by
  rw [localIntegralUnitAction_toAlgHom, ← integralPoints_genericHom,
    localIntegralScalar_generic]

end ThreeAdicPlan
