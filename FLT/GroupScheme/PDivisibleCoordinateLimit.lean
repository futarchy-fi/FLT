/-
Copyright (c) 2026 krandder. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: krandder
-/
module

public import FLT.GroupScheme.PDivisibleSystem
public import Mathlib.Algebra.Algebra.Pi

/-! # The inverse limit of the original coordinate algebras -/

@[expose] public noncomputable section
namespace ThreeAdicPlan.PDivisibleSystem
variable {R K : Type} [CommRing R] [IsLocalRing R] [Field K] [Algebra R K]
  [PerfectField K] [IsFractionRing R K] {p height : ℕ} [Fact p.Prime]
  (X : PDivisibleSystem R K p height)

/-- Compatible functions on the original finite levels. The transition maps are the
original closed inclusions, not the p-multiplication reductions. -/
def coordinateLimit : Subalgebra R (∀ n, (X.level n).CoordinateRing) where
  carrier := {x | ∀ {m n} (h : m ≤ n), X.inclusion h (x n) = x m}
  mul_mem' hx hy := by intro m n h; simp only [Pi.mul_apply, map_mul, hx h, hy h]
  add_mem' hx hy := by intro m n h; simp only [Pi.add_apply, map_add, hx h, hy h]
  algebraMap_mem' r := by intro m n h; exact (X.inclusion h).toAlgHom.commutes r

/-- Evaluation on the original finite coordinate algebra. -/
def coordinateEval (n : ℕ) : X.coordinateLimit →ₐ[R] (X.level n).CoordinateRing :=
  (Pi.evalAlgHom R _ n).comp X.coordinateLimit.val

/-- Evaluation respects the original closed inclusions. -/
theorem coordinateEval_inclusion {m n : ℕ} (h : m ≤ n) (x : X.coordinateLimit) :
    X.inclusion h (X.coordinateEval n x) = X.coordinateEval m x := x.property h

/-- The original finite evaluations separate functions in the inverse limit. -/
@[ext] theorem coordinateLimit_ext {x y : X.coordinateLimit}
    (h : ∀ n, X.coordinateEval n x = X.coordinateEval n y) : x = y :=
  Subtype.ext (funext h)

/-- A coherent family of algebra maps induces a map into the original coordinate limit. -/
def coordinateLift {A : Type*} [CommRing A] [Algebra R A]
    (f : ∀ n, A →ₐ[R] (X.level n).CoordinateRing)
    (hf : ∀ {m n} (h : m ≤ n) (a : A), X.inclusion h (f n a) = f m a) :
    A →ₐ[R] X.coordinateLimit where
  toFun a := ⟨fun n ↦ f n a, fun h ↦ hf h a⟩
  map_one' := Subtype.ext (funext fun n ↦ map_one (f n))
  map_mul' a b := Subtype.ext (funext fun n ↦ map_mul (f n) a b)
  map_zero' := Subtype.ext (funext fun n ↦ map_zero (f n))
  map_add' a b := Subtype.ext (funext fun n ↦ map_add (f n) a b)
  commutes' r := Subtype.ext (funext fun n ↦ (f n).commutes r)

/-- The universal lift has the specified finite evaluations. -/
theorem coordinateEval_lift {A : Type*} [CommRing A] [Algebra R A]
    (f : ∀ n, A →ₐ[R] (X.level n).CoordinateRing)
    (hf : ∀ {m n} (h : m ≤ n) (a : A), X.inclusion h (f n a) = f m a)
    (n : ℕ) (a : A) : X.coordinateEval n (X.coordinateLift f hf a) = f n a := rfl

/-- Compatible maps into the finite levels uniquely specify the map into the limit. -/
theorem coordinateLift_unique {A : Type*} [CommRing A] [Algebra R A]
    (f g : A →ₐ[R] X.coordinateLimit)
    (h : ∀ n, (X.coordinateEval n).comp f = (X.coordinateEval n).comp g) : f = g := by
  ext a n
  exact AlgHom.congr_fun (h n) a

end ThreeAdicPlan.PDivisibleSystem
