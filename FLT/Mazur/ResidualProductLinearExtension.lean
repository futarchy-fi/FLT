/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.ResidualProductExtension
public import Mathlib.LinearAlgebra.TensorProduct.Tower

/-!
# Linear residual extension and arbitrary scalar change

The residual summand is split over any compatible original scalar ring.
Its extension stays injective under every scalar change, including residue
fields. No flatness assumption is needed for this split summand.
-/

@[expose] public noncomputable section
open scoped TensorProduct
namespace FLT.Mazur.ResidualProductExtension
variable {B : Type*} [CommRing B] {ι : Type*} {C : Option ι → Type*}
  [∀ i, CommRing (C i)] (e : B ≃+* ∀ i, C i)
  (R : Type*) [CommRing R] [Algebra R B] [Algebra R (C none)]
  (hc : ∀ r : R, projection e (algebraMap R B r) = algebraMap R (C none) r)

/-- Actual residual restriction as a linear map over the original scalars. -/
def projectionLinear : B →ₗ[R] C none where
  __ := (projection e).toAddMonoidHom
  map_smul' r b := by
    change projection e (r • b) = r • projection e b
    simp only [Algebra.smul_def, map_mul, hc]

/-- Extension by zero is linear over the original scalar ring. -/
def extensionLinear : C none →ₗ[R] B where
  __ := extension e
  map_smul' r c := by
    change extension e (r • c) = r • extension e c
    simpa only [Algebra.smul_def, hc] using
      (mul_extension e (algebraMap R B r) c).symm

/-- The splitting is an equality of actual linear maps. -/
theorem projectionLinear_comp_extensionLinear :
    (projectionLinear e R hc).comp (extensionLinear e R hc) = LinearMap.id := by
  ext c
  exact projection_extension e c

/-- Every scalar change preserves the residual splitting, even without flatness. -/
theorem baseChange_projection_extension (T : Type*) [CommRing T] [Algebra R T] :
    ((projectionLinear e R hc).baseChange T).comp
      ((extensionLinear e R hc).baseChange T) = LinearMap.id := by
  rw [← LinearMap.baseChange_comp, projectionLinear_comp_extensionLinear]
  exact LinearMap.baseChange_id

/-- In particular residue scalar change cannot hide a residual coefficient. -/
theorem baseChange_extension_injective (T : Type*) [CommRing T] [Algebra R T] :
    Function.Injective ((extensionLinear e R hc).baseChange T) := by
  apply Function.LeftInverse.injective (f := (extensionLinear e R hc).baseChange T)
    (g := (projectionLinear e R hc).baseChange T)
  intro x
  exact LinearMap.congr_fun (baseChange_projection_extension e R hc T) x

variable {M : Type*} [AddCommGroup M] [Module R M] (F : M →ₗ[R] B)
  (hF : ∀ x i, e (F x) (some i) = 0)

include hF

/-- A map with zero nonresidual coordinates factors through the constructed residual summand. -/
theorem residual_factorization :
    (extensionLinear e R hc).comp ((projectionLinear e R hc).comp F) = F := by
  ext x
  exact extension_projection e (F x) (hF x)

/-- The exact factorization persists under arbitrary scalar change. -/
theorem baseChange_residual_factorization (T : Type*) [CommRing T] [Algebra R T] :
    ((extensionLinear e R hc).baseChange T).comp
      (((projectionLinear e R hc).comp F).baseChange T) = F.baseChange T := by
  rw [← LinearMap.baseChange_comp, residual_factorization e R hc F hF]

/-- Full correction equations reduce to residual equations after scalar change. -/
theorem baseChange_equation_iff (T : Type*) [CommRing T] [Algebra R T]
    (x : T ⊗[R] M) (c : T ⊗[R] C none) :
    F.baseChange T x = (extensionLinear e R hc).baseChange T c ↔
      ((projectionLinear e R hc).comp F).baseChange T x = c := by
  have hf := LinearMap.congr_fun (baseChange_residual_factorization e R hc F hF T) x
  rw [← hf]
  exact (baseChange_extension_injective e R hc T).eq_iff

end FLT.Mazur.ResidualProductExtension
