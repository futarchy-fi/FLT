/-
Copyright (c) 2026 krandder. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: krandder
-/
module

public import FLT.Mazur.WeierstrassModificationXFiberConic

/-!
# Recenter the second oriented tangent of the conic

The substitution w=v+a exchanges the two tangent origins and changes a to -a.
It preserves t and the middle-depth coefficient c, so no quadratic term is lost.
-/

@[expose] public noncomputable section

namespace FLT.Mazur.WeierstrassModificationX

set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true

variable {R : Type*} [CommRing R] (a c : R)

/-- Express the old slope as w-a in coordinates centered at the second tangent. -/
def conicTangentForward : ConicCoordinate a c →ₐ[R] ConicCoordinate (-a) c :=
  conicEvaluation a c (conicT (-a) c)
    (conicV (-a) c - algebraMap R _ a) (by
      have h := conic_relation (-a) c
      rw [map_neg] at h
      linear_combination h)

/-- Return from the second tangent coordinate w to the original slope v. -/
def conicTangentBackward : ConicCoordinate (-a) c →ₐ[R] ConicCoordinate a c :=
  conicEvaluation (-a) c (conicT a c) (conicV a c + algebraMap R _ a) (by
    rw [map_neg]
    linear_combination conic_relation a c)

/-- Recentering preserves the incidence ratio. -/
@[simp] theorem conicTangentForward_t :
    conicTangentForward a c (conicT a c) = conicT (-a) c := conicEvaluation_t _ _ _ _ _

/-- Recentering retains the exact original slope translation. -/
@[simp] theorem conicTangentForward_v : conicTangentForward a c (conicV a c) =
    conicV (-a) c - algebraMap R _ a := conicEvaluation_v _ _ _ _ _

/-- Returning to the original coordinates preserves the incidence ratio. -/
@[simp] theorem conicTangentBackward_t :
    conicTangentBackward a c (conicT (-a) c) = conicT a c := conicEvaluation_t _ _ _ _ _

/-- Returning to the original coordinates keeps the oriented translation. -/
@[simp] theorem conicTangentBackward_v : conicTangentBackward a c (conicV (-a) c) =
    conicV a c + algebraMap R _ a := conicEvaluation_v _ _ _ _ _

/-- The two conic equations are isomorphic by the actual slope translation. -/
def conicTangentEquiv : ConicCoordinate a c ≃ₐ[R] ConicCoordinate (-a) c := by
  apply AlgEquiv.ofAlgHom (conicTangentForward a c) (conicTangentBackward a c)
  · apply conic_hom_ext <;> simp
  · apply conic_hom_ext <;> simp

/-- The equivalence preserves the original incidence ratio. -/
@[simp] theorem conicTangentEquiv_t :
    conicTangentEquiv a c (conicT a c) = conicT (-a) c := conicTangentForward_t a c

/-- The equivalence sends the original second tangent to the new zero slope. -/
@[simp] theorem conicTangentEquiv_second :
    conicTangentEquiv a c (conicV a c + algebraMap R _ a) = conicV (-a) c := by
  change conicTangentForward a c (conicV a c + algebraMap R _ a) = conicV (-a) c
  simp

/-- The equivalence sends the original first tangent to the new other tangent. -/
@[simp] theorem conicTangentEquiv_v : conicTangentEquiv a c (conicV a c) =
    conicV (-a) c + algebraMap R _ (-a) := by
  change conicTangentForward a c (conicV a c) =
    conicV (-a) c + algebraMap R _ (-a)
  simp only [conicTangentForward_v, map_neg, sub_eq_add_neg]

end FLT.Mazur.WeierstrassModificationX
