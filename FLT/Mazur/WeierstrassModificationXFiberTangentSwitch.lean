/-
Copyright (c) 2026 krandder. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: krandder
-/
module

public import FLT.Mazur.WeierstrassModificationXFiberNormalForm

/-!
# Recenter the second oriented tangent of the full horizontal fiber

The substitution w=v+a exchanges the two tangent origins and changes a to -a.
It preserves t and the middle-depth coefficient c, so no quadratic term is lost.
-/

@[expose] public noncomputable section

namespace FLT.Mazur.WeierstrassModificationX

set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true

variable {R : Type*} [CommRing R] (a c : R)

/-- Express the old slope as w-a in coordinates centered at the second tangent. -/
def fiberTangentForward : FiberCoordinate a c →ₐ[R] FiberCoordinate (-a) c :=
  fiberEvaluation a c (fiberT (-a) c)
    (fiberV (-a) c - algebraMap R _ a) (by
      have h := fiber_relation (-a) c
      rw [map_neg] at h
      linear_combination h)

/-- Return from the second tangent coordinate w to the original slope v. -/
def fiberTangentBackward : FiberCoordinate (-a) c →ₐ[R] FiberCoordinate a c :=
  fiberEvaluation (-a) c (fiberT a c) (fiberV a c + algebraMap R _ a) (by
    rw [map_neg]
    linear_combination fiber_relation a c)

/-- Recentering preserves the incidence ratio. -/
@[simp] theorem fiberTangentForward_t :
    fiberTangentForward a c (fiberT a c) = fiberT (-a) c := fiberEvaluation_t _ _ _ _ _

/-- Recentering retains the exact original slope translation. -/
@[simp] theorem fiberTangentForward_v : fiberTangentForward a c (fiberV a c) =
    fiberV (-a) c - algebraMap R _ a := fiberEvaluation_v _ _ _ _ _

/-- Returning to the original coordinates preserves the incidence ratio. -/
@[simp] theorem fiberTangentBackward_t :
    fiberTangentBackward a c (fiberT (-a) c) = fiberT a c := fiberEvaluation_t _ _ _ _ _

/-- Returning to the original coordinates keeps the oriented translation. -/
@[simp] theorem fiberTangentBackward_v : fiberTangentBackward a c (fiberV (-a) c) =
    fiberV a c + algebraMap R _ a := fiberEvaluation_v _ _ _ _ _

/-- The two complete fiber equations are isomorphic by the actual slope translation. -/
def fiberTangentEquiv : FiberCoordinate a c ≃ₐ[R] FiberCoordinate (-a) c := by
  apply AlgEquiv.ofAlgHom (fiberTangentForward a c) (fiberTangentBackward a c)
  · apply fiber_hom_ext <;> simp
  · apply fiber_hom_ext <;> simp

/-- The equivalence preserves the original incidence ratio. -/
@[simp] theorem fiberTangentEquiv_t :
    fiberTangentEquiv a c (fiberT a c) = fiberT (-a) c := fiberTangentForward_t a c

/-- The equivalence sends the original second tangent to the new zero slope. -/
@[simp] theorem fiberTangentEquiv_second :
    fiberTangentEquiv a c (fiberV a c + algebraMap R _ a) = fiberV (-a) c := by
  change fiberTangentForward a c (fiberV a c + algebraMap R _ a) = fiberV (-a) c
  simp

/-- The equivalence sends the original first tangent to the new other tangent. -/
@[simp] theorem fiberTangentEquiv_v : fiberTangentEquiv a c (fiberV a c) =
    fiberV (-a) c + algebraMap R _ (-a) := by
  change fiberTangentForward a c (fiberV a c) =
    fiberV (-a) c + algebraMap R _ (-a)
  simp only [fiberTangentForward_v, map_neg, sub_eq_add_neg]

end FLT.Mazur.WeierstrassModificationX
