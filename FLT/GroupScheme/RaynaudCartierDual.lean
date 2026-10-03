/-
Copyright (c) 2026 krandder. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: krandder
-/
module

public import FLT.GroupScheme.FiniteFlatScalarExtension
public import FLT.GroupScheme.CartierDualEtale
public import FLT.GroupScheme.CartierDualBaseChangeHopf
public import FLT.GroupScheme.CartierDualMaps
public import Mathlib.LinearAlgebra.FreeModule.PID

/-!
# Cartier duals of finite flat models over a principal domain

The dual uses the actual integral dual Hopf algebra, and its generic fibre
is étale in characteristic zero. No extension theorem is used.
-/

@[expose] public noncomputable section

open scoped TensorProduct
namespace ThreeAdicPlan

variable {R K : Type} [CommRing R] [Field K] [Algebra R K]
  [IsDomain R] [IsPrincipalIdealRing R] [IsFractionRing R K] [CharZero K]

/-- The actual integral Cartier dual, with its geometric generic points. -/
def FF.cartierDual (X : FF R K) : FF R K := by
  let : Algebra.Etale K (HopfAlgebra.CartierDual K (K ⊗[R] X.CoordinateRing)) :=
    HopfAlgebra.CartierDual.etale K (K ⊗[R] X.CoordinateRing)
  let : Algebra.Etale K (K ⊗[R] HopfAlgebra.CartierDual R X.CoordinateRing) :=
    Algebra.Etale.of_equiv (HopfAlgebra.CartierDual.baseChangeAlgEquiv K).symm
  exact FF.ofCoordinateRing (HopfAlgebra.CartierDual R X.CoordinateRing)

/-- The generic coordinates of the integral dual are the dual generic coordinates. -/
def FF.cartierDualGenericEquiv (X : FF R K) :
    K ⊗[R] X.cartierDual.CoordinateRing ≃ₐc[K]
      HopfAlgebra.CartierDual K (K ⊗[R] X.CoordinateRing) :=
  HopfAlgebra.CartierDual.baseChangeBialgEquiv K

/-- Cartier duality reverses integral model morphisms. -/
def ModelHom.cartierDual {X Y : FF R K} (f : ModelHom X Y) :
    ModelHom Y.cartierDual X.cartierDual :=
  HopfAlgebra.CartierDual.bialgMap f

/-- Integral double duality is evaluation. -/
def FF.cartierBidualEquiv (X : FF R K) :
    X.CoordinateRing ≃ₐc[R] X.cartierDual.cartierDual.CoordinateRing :=
  HopfAlgebra.CartierDual.bidualEquiv

/-- Dualizing an integral map evaluates by precomposition. -/
@[simp] theorem ModelHom.cartierDual_apply {X Y : FF R K} (f : ModelHom X Y)
    (φ : HopfAlgebra.CartierDual R X.CoordinateRing) (y : Y.CoordinateRing) :
    (show HopfAlgebra.CartierDual R Y.CoordinateRing from f.cartierDual φ) y = φ (f y) := rfl

end ThreeAdicPlan
