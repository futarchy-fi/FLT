/-
Copyright (c) 2026 krandder. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: krandder
-/
module

public import FLT.GroupScheme.PDivisibleCotangentLimit
public import FLT.GroupScheme.PDivisibleVariableHeightHom

/-! # Cotangent maps for systems of different heights -/

@[expose] public noncomputable section
namespace ThreeAdicPlan.PDivisibleSystem
variable {R K : Type} [CommRing R] [IsLocalRing R] [Field K] [Algebra R K]
  [PerfectField K] [IsFractionRing R K] {p h₁ h₂ : ℕ} [Fact p.Prime]
  {X : PDivisibleSystem R K p h₁} {Y : PDivisibleSystem R K p h₂}

/-- An original system morphism acts contravariantly on the cotangent limit. -/
def VariableHeightHom.cotangentMap (f : VariableHeightHom X Y) :
    Y.cotangentLimit →ₗ[R] X.cotangentLimit :=
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
theorem VariableHeightHom.cotangentMap_eval (f : VariableHeightHom X Y)
    (x : Y.cotangentLimit) (n : ℕ) :
    X.cotangentEval n (f.cotangentMap x) =
      ModelHom.cotangentMap (f.app n) (Y.cotangentEval n x) := rfl

/-- Levelwise cotangent isomorphisms identify the actual inverse limits. -/
theorem VariableHeightHom.cotangentMap_bijective (f : VariableHeightHom X Y)
    (hf : ∀ n, Function.Bijective (ModelHom.cotangentMap (f.app n))) :
    Function.Bijective f.cotangentMap := by
  constructor
  · intro x y h
    apply Y.cotangentLimit_ext
    intro n
    exact (hf n).1 (congrArg (X.cotangentEval n) h)
  · intro x
    let e (n : ℕ) := LinearEquiv.ofBijective (ModelHom.cotangentMap (f.app n)) (hf n)
    let y (n : ℕ) := (e n).symm (X.cotangentEval n x)
    have hy (n : ℕ) : ModelHom.cotangentMap (f.app n) (y n) = X.cotangentEval n x :=
      (e n).apply_symm_apply _
    have hc : y ∈ Y.cotangentLimit := by
      intro m n h
      apply (hf m).1
      have he := congrArg (ModelHom.cotangentMap (X := X.level m) (Y := Y.level n))
        (f.inclusion_naturality h)
      rw [ModelHom.cotangentMap_comp, ModelHom.cotangentMap_comp] at he
      have hv := congrArg (fun k ↦ k (y n)) he
      change ModelHom.cotangentMap (f.app m) (Y.cotangentRestriction h (y n)) =
        ModelHom.cotangentMap (f.app m) (y m)
      change X.cotangentRestriction h (ModelHom.cotangentMap (f.app n) (y n)) =
        ModelHom.cotangentMap (f.app m) (Y.cotangentRestriction h (y n)) at hv
      rw [← hv, hy, X.cotangentEval_restriction, hy]
    exact ⟨⟨y, hc⟩, X.cotangentLimit_ext hy⟩
end ThreeAdicPlan.PDivisibleSystem
