/-
Copyright (c) 2026 krandder. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: krandder
-/
module

public import FLT.GroupScheme.PDivisibleSystem

/-! # Coherent point sequences of a p-divisible system

This constructs the additive inverse limit of the actual reduction maps.
Its p-adic module structure and comparison with an original lattice are
separate theorems; neither is part of the definition.
-/

@[expose] public noncomputable section
namespace ThreeAdicPlan.PDivisibleSystem
variable {R K : Type} [CommRing R] [IsLocalRing R] [Field K] [Algebra R K]
  [PerfectField K] [IsFractionRing R K] {p height : ℕ} [Fact p.Prime]
  (X : PDivisibleSystem R K p height)

/-- Compatible sequences under the specified integral reductions. -/
def tateSequences : AddSubgroup (∀ n, (X.level n).Points) where
  carrier := {x | ∀ {m n} (h : m ≤ n), genericHom (X.reduction h) (x n) = x m}
  zero_mem' := by intro m n h; exact map_zero _
  add_mem' := by
    intro x y hx hy m n h
    change genericHom (X.reduction h) (x n + y n) = x m + y m
    rw [map_add, hx h, hy h]
  neg_mem' := by
    intro x hx m n h
    change genericHom (X.reduction h) (-x n) = -x m
    rw [map_neg, hx h]

/-- Evaluation on a finite level is an additive morphism. -/
def tateEval (n : ℕ) : X.tateSequences →+ (X.level n).Points where
  toFun x := x.val n
  map_zero' := rfl
  map_add' _ _ := rfl

/-- All evaluation maps respect the original reductions. -/
theorem tateEval_reduction {m n : ℕ} (h : m ≤ n) (x : X.tateSequences) :
    genericHom (X.reduction h) (X.tateEval n x) = X.tateEval m x := x.property h

/-- Equality in the limit is detected by its finite-level evaluations. -/
@[ext] theorem tate_ext {x y : X.tateSequences}
    (h : ∀ n, X.tateEval n x = X.tateEval n y) : x = y :=
  Subtype.ext (funext h)

/-- A coherent family of maps into the levels induces a map into the limit. -/
def tateLift {A : Type*} [AddCommGroup A] (f : ∀ n, A →+ (X.level n).Points)
    (hf : ∀ {m n} (h : m ≤ n) (a : A), genericHom (X.reduction h) (f n a) = f m a) :
    A →+ X.tateSequences where
  toFun a := ⟨fun n ↦ f n a, fun h ↦ hf h a⟩
  map_zero' := by apply Subtype.ext; funext n; exact map_zero _
  map_add' a b := by apply Subtype.ext; funext n; exact map_add _ a b

/-- The induced map has the prescribed coordinates. -/
@[simp] theorem tateEval_lift {A : Type*} [AddCommGroup A]
    (f : ∀ n, A →+ (X.level n).Points)
    (hf : ∀ {m n} (h : m ≤ n) (a : A), genericHom (X.reduction h) (f n a) = f m a)
    (n : ℕ) (a : A) : X.tateEval n (X.tateLift f hf a) = f n a := rfl

/-- The coordinate condition uniquely specifies the induced additive map. -/
theorem tateLift_unique {A : Type*} [AddCommGroup A]
    (f : ∀ n, A →+ (X.level n).Points)
    (hf : ∀ {m n} (h : m ≤ n) (a : A), genericHom (X.reduction h) (f n a) = f m a)
    (g : A →+ X.tateSequences) (hg : ∀ n a, X.tateEval n (g a) = f n a) :
    g = X.tateLift f hf := by
  ext a n
  exact hg n a

end ThreeAdicPlan.PDivisibleSystem
