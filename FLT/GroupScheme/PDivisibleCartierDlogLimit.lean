/-
Copyright (c) 2026 krandder. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: krandder
-/
module

public import FLT.GroupScheme.PDivisibleCartierTatePairing
public import FLT.GroupScheme.RaynaudIntegralCartier
public import FLT.GroupScheme.FiniteFlatCartierDifferential
public import FLT.GroupScheme.PDivisibleCotangentTransitions

/-! # Actual dual Tate vectors give coherent integral Cartier cotangent tensors -/

@[expose] public noncomputable section
open scoped TensorProduct
namespace ThreeAdicPlan.PDivisibleSystem
variable {R K S : Type} [CommRing R] [IsLocalRing R] [Field K] [Algebra R K]
  [IsDomain R] [IsPrincipalIdealRing R] [IsFractionRing R K] [CharZero K]
  [CommRing S] [Algebra R S] {p height : ℕ} [Fact p.Prime]
  (X : PDivisibleSystem R K p height)

/-- The actual dual Tate coordinate extends uniquely to the integral closure. -/
def cartierTateIntegralCoordinate (n : ℕ) (y : X.CartierTate) :
    HopfAlgebra.CartierDual R (X.level n).CoordinateRing →ₐ[R]
      integralClosure R (AlgebraicClosure K) :=
  (X.level n).cartierDual.integralPointCoordinate (X.cartierTateEval n y)

/-- Integral dual coordinates obey the original inclusion's transposed transition. -/
theorem cartierTateIntegralCoordinate_transition {m n : ℕ} (h : m ≤ n) (y : X.CartierTate) :
    (X.cartierTateIntegralCoordinate n y).comp
        (HopfAlgebra.CartierDual.map (X.inclusion h)) =
      X.cartierTateIntegralCoordinate m y := by
  have he := (X.inclusion h).cartierDual.integralPointCoordinate_genericHom
    (X.cartierTateEval n y)
  rw [X.cartierTateEval_transition h y] at he
  exact he.symm

/-- The original finite character gives its actual cotangent tensor with integral coefficients. -/
def cartierTateDlogAt (q : integralClosure R (AlgebraicClosure K) →ₐ[R] S)
    (n : ℕ) (y : X.CartierTate) : X.LevelCotangent n ⊗[R] S :=
  (X.level n).cartierDlog (q.comp (X.cartierTateIntegralCoordinate n y))

/-- Dlog commutes with the specified original cotangent restriction. -/
theorem cartierTateDlogAt_transition (q : integralClosure R (AlgebraicClosure K) →ₐ[R] S)
    {m n : ℕ} (h : m ≤ n) (y : X.CartierTate) :
    (X.cotangentRestriction h).rTensor S (X.cartierTateDlogAt q n y) =
      X.cartierTateDlogAt q m y := by
  unfold cartierTateDlogAt
  rw [show X.cotangentRestriction h = (X.inclusion h).cotangentMap from rfl,
    ModelHom.cartierDlog_naturality]
  congr 1
  rw [AlgHom.comp_assoc, X.cartierTateIntegralCoordinate_transition h y]

/-- The actual inverse limit of the integral cotangent tensors, with no comparison assumed. -/
def CartierCotangentSequences : Submodule R (∀ n, X.LevelCotangent n ⊗[R] S) where
  carrier := {v | ∀ {m n} (h : m ≤ n), (X.cotangentRestriction h).rTensor S (v n) = v m}
  zero_mem' := by intro m n h; simp
  add_mem' hv hw := by intro m n h; simp only [Pi.add_apply, map_add, hv h, hw h]
  smul_mem' r v hv := by intro m n h; simp only [Pi.smul_apply, map_smul, hv h]

/-- A dual Tate vector determines a coherent sequence of its original integral dlog tensors. -/
def cartierTateDlog (q : integralClosure R (AlgebraicClosure K) →ₐ[R] S)
    (y : X.CartierTate) : X.CartierCotangentSequences (S := S) :=
  ⟨fun n ↦ X.cartierTateDlogAt q n y, fun h ↦ X.cartierTateDlogAt_transition q h y⟩

/-- Coefficient specialization preserves each actual finite tensor. -/
theorem cartierTateDlogAt_coefficients {T : Type} [CommRing T] [Algebra R T]
    (q : integralClosure R (AlgebraicClosure K) →ₐ[R] S) (f : S →ₐ[R] T)
    (n : ℕ) (y : X.CartierTate) :
    f.toLinearMap.lTensor _ (X.cartierTateDlogAt q n y) =
      X.cartierTateDlogAt (f.comp q) n y :=
  HopfAlgebra.CartierDual.testDlog_coefficients f (q.comp (X.cartierTateIntegralCoordinate n y))

end ThreeAdicPlan.PDivisibleSystem
