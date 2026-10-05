/-
Copyright (c) 2026 krandder. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: krandder
-/
module

public import FLT.GroupScheme.RationalPlaceRootTwist
public import FLT.GroupScheme.RationalPlaceTateRootDuality
public import Mathlib.LinearAlgebra.Dual.Lemmas

/-! # Orienting original Cartier duality toward the original Tate realization -/

@[expose] public noncomputable section
set_option backward.isDefEq.respectTransparency false
open PadicHodgeTheory
open scoped TensorProduct
attribute [local instance 2000] IsDedekindDomain.HeightOneSpectrum.adicCompletion.instField
  IsDedekindDomain.HeightOneSpectrum.instAlgebraAdicCompletion
attribute [local instance 2000] Algebra.toModule Algebra.toSMul
namespace ThreeAdicPlan
variable {p height : ℕ} [Fact p.Prime]
variable (X : PDivisibleSystem ((LocalCyclotomic.rationalPlace p).adicCompletionIntegers ℚ)
  ((LocalCyclotomic.rationalPlace p).adicCompletion ℚ) p height)

/-- The original Cartier duality in the prescribed cyclotomic coordinates. -/
def rationalPlaceTateScalarDuality : RationalPlaceTateRealization X.cartierDual ≃ₗ[ℂ_[p]]
    Module.Dual ℂ_[p] (RationalPlaceTateRealization X) :=
  (rationalPlaceTateRootDuality X).trans
    (LinearEquiv.arrowCongr (LinearEquiv.refl ℂ_[p] _) (rationalPlaceRootCoordinate p))

/-- Scalar-valued duality is the coordinate of the actual root-valued pairing. -/
theorem rationalPlaceTateScalarDuality_apply
    (y : RationalPlaceTateRealization X.cartierDual) (x : RationalPlaceTateRealization X) :
    rationalPlaceTateScalarDuality X y x =
      rationalPlaceRootCoordinate p (rationalPlaceTateRootDuality X y x) := rfl

/-- Perfect duality identifies the original Tate space with the dual Cartier space. -/
def rationalPlaceTateLeftDuality : RationalPlaceTateRealization X ≃ₗ[ℂ_[p]]
    Module.Dual ℂ_[p] (RationalPlaceTateRealization X.cartierDual) := by
  let : Module.Finite ℂ_[p] (RationalPlaceTateRealization X) :=
    rationalPlace_tateRealization_finite X
  let : Module.Free ℂ_[p] (RationalPlaceTateRealization X) := Module.Free.of_divisionRing _ _
  let : Module.IsReflexive ℂ_[p] (RationalPlaceTateRealization X) :=
    Module.IsReflexive.of_finite_of_free _ _
  exact (Module.evalEquiv ℂ_[p] (RationalPlaceTateRealization X)).trans
    (rationalPlaceTateScalarDuality X).dualMap

/-- The left-oriented identification evaluates the same original Cartier pairing. -/
theorem rationalPlaceTateLeftDuality_apply
    (x : RationalPlaceTateRealization X) (y : RationalPlaceTateRealization X.cartierDual) :
    rationalPlaceTateLeftDuality X x y = rationalPlaceTateScalarDuality X y x := rfl

/-- Actual Cartier vectors separate all vectors of the original Tate realization. -/
theorem rationalPlaceTateScalarDuality_separates {x z : RationalPlaceTateRealization X}
    (h : ∀ y, rationalPlaceTateScalarDuality X y x = rationalPlaceTateScalarDuality X y z) :
    x = z := by
  apply (rationalPlaceTateLeftDuality X).injective
  exact LinearMap.ext h
end ThreeAdicPlan
