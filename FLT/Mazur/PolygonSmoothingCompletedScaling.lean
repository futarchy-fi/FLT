/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.PolygonSmoothingNodeScaling

/-!
# Reciprocal scaling on the arithmetic node completion

The action is constructed from the full coordinate-ideal powers. Evaluation
recovers the original finite-neighborhood action, with no radical replacement.
-/

@[expose] public noncomputable section
namespace FLT.Mazur.PolygonSmoothing
set_option backward.isDefEq.respectTransparency false
variable {R : Type*} [CommRing R] (t : R)
local notation "I" => coordinateIdeal t
local notation "A" => ChartRing t

/-- The actual inverse-limit automorphism of the full arithmetic node. -/
def completedScale (a : Rˣ) : AdicCompletion (I) (A) ≃ₐ[R] AdicCompletion (I) (A) :=
  AdicCompletionAlgEquiv.equivalence (reciprocalScaleEquiv t a) (I) (I)
    (reciprocalScale_coordinateIdeal t a).symm

/-- Each evaluation is exactly the full original neighborhood automorphism. -/
@[simp] theorem completedScale_eval (a : Rˣ) (m : ℕ) (x : AdicCompletion (I) (A)) :
    AdicCompletion.evalₐ (I) m (completedScale t a x) =
      nodeScale t a m (AdicCompletion.evalₐ (I) m x) :=
  AdicCompletionAlgEquiv.eval_map (reciprocalScaleEquiv t a) (I) (I)
    (reciprocalScale_coordinateIdeal t a).symm m x

/-- Completion retains scaling on every element of the original arithmetic ring. -/
theorem completedScale_of (a : Rˣ) (x : A) :
    completedScale t a (AdicCompletion.of (I) (A) x) =
      AdicCompletion.of (I) (A) (reciprocalScale t a x) := by
  apply AdicCompletion.ext_evalₐ
  intro m
  simp only [completedScale_eval, AdicCompletion.evalₐ_of, nodeScale_mk]

/-- The first original completed branch coordinate has weight one. -/
theorem completedScale_left (a : Rˣ) :
    completedScale t a (AdicCompletion.of (I) (A) (leftCoordinate t)) =
      AdicCompletion.of (I) (A) (algebraMap R (A) a * leftCoordinate t) := by
  rw [completedScale_of, reciprocalScale_left]

/-- The second original completed branch coordinate has inverse weight. -/
theorem completedScale_right (a : Rˣ) :
    completedScale t a (AdicCompletion.of (I) (A) (rightCoordinate t)) =
      AdicCompletion.of (I) (A) (algebraMap R (A) ↑a⁻¹ * rightCoordinate t) := by
  rw [completedScale_of, reciprocalScale_right]

/-- The unit acts identically on the full completion. -/
@[simp] theorem completedScale_one : completedScale t 1 = AlgEquiv.refl := by
  ext x : 1
  apply AdicCompletion.ext_evalₐ
  intro m
  rw [completedScale_eval, nodeScale_one]
  rfl

/-- The constructed completed maps satisfy the action multiplication law. -/
theorem completedScale_mul (a b : Rˣ) (x : AdicCompletion (I) (A)) :
    completedScale t (a * b) x = completedScale t a (completedScale t b x) := by
  apply AdicCompletion.ext_evalₐ
  intro m
  simp only [completedScale_eval, nodeScale_mul]

/-- Inversion of the parameter gives the actual inverse on the full completion. -/
theorem completedScale_inv (a : Rˣ) : (completedScale t a).symm = completedScale t a⁻¹ := by
  ext x : 1
  apply (completedScale t a).injective
  rw [AlgEquiv.apply_symm_apply, ← completedScale_mul, mul_inv_cancel, completedScale_one]
  rfl

end FLT.Mazur.PolygonSmoothing
