/-
Copyright (c) 2026 krandder. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: krandder
-/
module

public import FLT.GroupScheme.PDivisibleCotangentLimitFinite
public import Mathlib.LinearAlgebra.FreeModule.PID
public import Mathlib.RingTheory.Noetherian.Basic

/-! # The integral linear dual of the original cotangent limit

This constructs the algebraic tangent module. It does not identify its reduction
with all torsion-valued functionals; that requires additional cotangent freeness.
-/

@[expose] public noncomputable section
namespace ThreeAdicPlan.PDivisibleSystem
variable {R K : Type} [CommRing R] [IsLocalRing R] [Field K] [Algebra R K]
  [PerfectField K] [IsFractionRing R K] {p height : ℕ} [Fact p.Prime]
  (X : PDivisibleSystem R K p height)

/-- The integral algebraic tangent is the linear dual of the actual cotangent inverse limit. -/
abbrev IntegralTangent := Module.Dual R X.cotangentLimit

/-- Evaluation of the tangent on the actual cotangent limit is the original linear pairing. -/
def integralTangentPairing : X.IntegralTangent →ₗ[R] X.cotangentLimit →ₗ[R] R := LinearMap.id

/-- Over a Noetherian original base, the tangent module is finitely generated. -/
theorem integralTangent_finite [IsNoetherianRing R] (e : R ≃+* ℤ_[p]) :
    Module.Finite R X.IntegralTangent := by
  let := X.cotangentLimit_finite e
  infer_instance

/-- Over the original principal ideal domain the integral tangent is free. -/
theorem integralTangent_free [IsDomain R] [IsPrincipalIdealRing R] (e : R ≃+* ℤ_[p]) :
    Module.Free R X.IntegralTangent := by
  let := X.integralTangent_finite e
  infer_instance

variable {X} {Y : PDivisibleSystem R K p height}

/-- An original system morphism acts covariantly on the integral algebraic tangent. -/
def Hom.integralTangentMap (f : Hom X Y) : X.IntegralTangent →ₗ[R] Y.IntegralTangent :=
  (LinearMap.llcomp R Y.cotangentLimit X.cotangentLimit R).flip f.cotangentMap

/-- The tangent map is adjoint to the same original cotangent map. -/
theorem Hom.integralTangentMap_apply (f : Hom X Y) (d : X.IntegralTangent)
    (y : Y.cotangentLimit) : f.integralTangentMap d y = d (f.cotangentMap y) := rfl

end ThreeAdicPlan.PDivisibleSystem
