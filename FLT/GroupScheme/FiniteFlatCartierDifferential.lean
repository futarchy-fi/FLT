/-
Copyright (c) 2026 krandder. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: krandder
-/
module

public import FLT.GroupScheme.CartierDualElementNaturality
public import FLT.GroupScheme.CartierSquareZeroDifferential
public import FLT.GroupScheme.FiniteFlatTangentNaturality

/-! # Original finite model morphisms preserve the actual Cartier differential -/

@[expose] public noncomputable section
open scoped TensorProduct
namespace ThreeAdicPlan
open HopfAlgebra.CartierDual
variable {R K S : Type} [CommRing R] [IsLocalRing R] [Field K] [Algebra R K]
  [CommRing S] [Algebra R S]
local instance differentialCoordinateFree (X : FF R K) : Module.Free R X.CoordinateRing :=
  Module.free_of_flat_of_isLocalRing

/-- The original model's actual cotangent tensor of an integral Cartier character. -/
def FF.cartierDlog (X : FF R K)
    (ψ : HopfAlgebra.CartierDual R X.CoordinateRing →ₐ[R] S) : X.Cotangent ⊗[R] S :=
  testDlog ψ

/-- The actual original model morphism transports the character's cotangent tensor. -/
theorem ModelHom.cartierDlog_naturality {X Y : FF R K} (f : ModelHom X Y)
    (ψ : HopfAlgebra.CartierDual R Y.CoordinateRing →ₐ[R] S) :
    f.cotangentMap.rTensor S (Y.cartierDlog ψ) = X.cartierDlog (ψ.comp (map f)) := by
  unfold FF.cartierDlog testDlog
  rw [← testDualElement_naturality f ψ]
  generalize testDualElement ψ = t
  induction t using TensorProduct.inductionOn with
  | tmul a s =>
    simp only [LinearMap.rTensor_tmul, ModelHom.cotangentMap_projection]
    rfl
  | add t u ht hu => simp only [map_add, ht, hu]

/-- Differentiating a character commutes with the given original tangent map. -/
theorem ModelHom.cartierLogDifferential_naturality {X Y : FF R K} (f : ModelHom X Y)
    (ψ : HopfAlgebra.CartierDual R Y.CoordinateRing →ₐ[R] S) (d : X.Tangent (M := S)) :
    testLogDifferential (ψ.comp (map f)) d = testLogDifferential ψ (f.tangentMap d) :=
  testEvaluation_naturality f ψ d.val

/-- Pairing the cotangent tensor is exactly the logarithmic differential on original tangents. -/
theorem FF.cartierDlog_pairing (X : FF R K)
    (ψ : HopfAlgebra.CartierDual R X.CoordinateRing →ₐ[R] S)
    (d : X.Cotangent →ₗ[R] S) :
    LinearMap.mul' R S (d.rTensor S (X.cartierDlog ψ)) =
      testLogDifferential ψ (X.cotangentTangentEquiv d) :=
  testDlogPairing_eq ψ d

end ThreeAdicPlan
