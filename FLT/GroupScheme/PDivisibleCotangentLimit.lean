/-
Copyright (c) 2026 krandder. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: krandder
-/
module

public import FLT.GroupScheme.PDivisibleCotangentTransitions

/-! # The inverse limit of the actual integral cotangent modules -/

@[expose] public noncomputable section
namespace ThreeAdicPlan.PDivisibleSystem
variable {R K : Type} [CommRing R] [IsLocalRing R] [Field K] [Algebra R K]
  [PerfectField K] [IsFractionRing R K] {p height : ℕ} [Fact p.Prime]
  (X : PDivisibleSystem R K p height)

/-- Compatible cotangents under the original closed level inclusions. -/
def cotangentLimit : Submodule R (∀ n, X.LevelCotangent n) where
  carrier := {x | ∀ {m n} (h : m ≤ n), X.cotangentRestriction h (x n) = x m}
  zero_mem' := by intro m n h; exact map_zero _
  add_mem' hx hy := by intro m n h; simp only [Pi.add_apply, map_add, hx h, hy h]
  smul_mem' r x hx := by intro m n h; simp only [Pi.smul_apply, map_smul, hx h]

/-- The original level projection from the cotangent inverse limit. -/
def cotangentEval (n : ℕ) : X.cotangentLimit →ₗ[R] X.LevelCotangent n :=
  (LinearMap.proj n).comp X.cotangentLimit.subtype

/-- The constructed projections commute with the specified transitions. -/
theorem cotangentEval_restriction {m n : ℕ} (h : m ≤ n) (x : X.cotangentLimit) :
    X.cotangentRestriction h (X.cotangentEval n x) = X.cotangentEval m x := x.property h

/-- Equality in this limit is determined by its actual level projections. -/
@[ext] theorem cotangentLimit_ext {x y : X.cotangentLimit}
    (h : ∀ n, X.cotangentEval n x = X.cotangentEval n y) : x = y :=
  Subtype.ext (funext h)

/-- Compatible linear maps have a unique map into the actual cotangent inverse limit. -/
def cotangentLift {M : Type*} [AddCommGroup M] [Module R M]
    (f : ∀ n, M →ₗ[R] X.LevelCotangent n)
    (hf : ∀ {m n} (h : m ≤ n) (x : M), X.cotangentRestriction h (f n x) = f m x) :
    M →ₗ[R] X.cotangentLimit :=
  (LinearMap.pi f).codRestrict X.cotangentLimit (fun x ↦ fun h ↦ hf h x)

/-- The lift has the prescribed projection at each level. -/
theorem cotangentEval_lift {M : Type*} [AddCommGroup M] [Module R M]
    (f : ∀ n, M →ₗ[R] X.LevelCotangent n)
    (hf : ∀ {m n} (h : m ≤ n) (x : M), X.cotangentRestriction h (f n x) = f m x)
    (n : ℕ) (x : M) : X.cotangentEval n (X.cotangentLift f hf x) = f n x := rfl

variable {X} {Y Z : PDivisibleSystem R K p height}

/-- An original system morphism acts contravariantly on the cotangent limit. -/
def Hom.cotangentMap (f : Hom X Y) : Y.cotangentLimit →ₗ[R] X.cotangentLimit :=
  X.cotangentLift (fun n ↦ (ModelHom.cotangentMap (f.app n)).comp (Y.cotangentEval n)) (by
    intro m n h x
    have he := congrArg (ModelHom.cotangentMap (X := X.level m) (Y := Y.level n))
      (f.inclusion_naturality h)
    rw [ModelHom.cotangentMap_comp, ModelHom.cotangentMap_comp] at he
    change ((ModelHom.cotangentMap (X.inclusion h)).comp
      (ModelHom.cotangentMap (f.app n))) (Y.cotangentEval n x) = _
    rw [he]
    exact congrArg (ModelHom.cotangentMap (f.app m)) (Y.cotangentEval_restriction h x))

/-- Evaluation of the induced map is the specified integral cotangent map. -/
theorem Hom.cotangentMap_eval (f : Hom X Y) (x : Y.cotangentLimit) (n : ℕ) :
    X.cotangentEval n (f.cotangentMap x) =
      ModelHom.cotangentMap (f.app n) (Y.cotangentEval n x) := rfl

/-- Identity systems induce identity maps of the actual cotangent limit. -/
theorem Hom.cotangentMap_id : (Hom.id X).cotangentMap = LinearMap.id := by
  ext x n
  change ModelHom.cotangentMap (BialgHom.id R (X.level n).CoordinateRing) _ = _
  rw [ModelHom.cotangentMap_id]
  rfl

/-- Composition is contravariant on the actual cotangent limit. -/
theorem Hom.cotangentMap_comp (f : Hom X Y) (g : Hom Y Z) :
    (f.comp g).cotangentMap = f.cotangentMap.comp g.cotangentMap := by
  ext x n
  change ModelHom.cotangentMap ((f.app n).comp (g.app n)) _ = _
  rw [ModelHom.cotangentMap_comp]
  rfl

end ThreeAdicPlan.PDivisibleSystem
