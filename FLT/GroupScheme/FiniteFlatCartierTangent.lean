/-
Copyright (c) 2026 krandder. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: krandder
-/
module

public import FLT.GroupScheme.CartierDualTangent
public import FLT.GroupScheme.FiniteFlatTangentNaturality

/-! # Naturality of tangent identification with the actual Cartier dual -/

@[expose] public noncomputable section
namespace ThreeAdicPlan
open HopfAlgebra.CartierDual
variable {R K : Type} [CommRing R] [IsLocalRing R] [Field K] [Algebra R K]

/-- Finite flat coordinates over this local base are free. -/
local instance finiteFlatTangentCoordinateFree (X : FF R K) : Module.Free R X.CoordinateRing :=
  Module.free_of_flat_of_isLocalRing

/-- A finite-flat tangent is a primitive element of the original integral Cartier dual. -/
def FF.tangentCartierEquiv (X : FF R K) :
    X.Tangent (M := R) ≃ₗ[R]
      Coalgebra.skewPrimitive R (1 : HopfAlgebra.CartierDual R X.CoordinateRing) 1 :=
  tangentPrimitiveEquiv

/-- This tangent/Cartier identification uses the original coordinate evaluation. -/
theorem FF.tangentCartierEquiv_apply (X : FF R K) (d : X.Tangent (M := R))
    (a : X.CoordinateRing) : (X.tangentCartierEquiv d).val a = d.val a := rfl

/-- Original integral morphisms intertwine tangent maps and their actual Cartier transposes. -/
theorem ModelHom.tangentCartier_naturality {X Y : FF R K} (f : ModelHom X Y)
    (d : X.Tangent (M := R)) :
    (Y.tangentCartierEquiv (f.tangentMap d)).val =
      bialgMap f (X.tangentCartierEquiv d).val := by
  apply WithConv.ext
  ext a
  rfl

/-- Cotangent duality and Cartier duality commute with the same original coordinate map. -/
theorem ModelHom.cotangentCartier_naturality {X Y : FF R K} (f : ModelHom X Y)
    (d : X.Cotangent →ₗ[R] R) :
    (Y.tangentCartierEquiv (Y.cotangentTangentEquiv (d.comp f.cotangentMap))).val =
      bialgMap f (X.tangentCartierEquiv (X.cotangentTangentEquiv d)).val := by
  rw [← ModelHom.cotangentTangent_naturality, ModelHom.tangentCartier_naturality]

end ThreeAdicPlan
