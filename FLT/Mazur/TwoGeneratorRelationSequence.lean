/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.TwoGeneratorRelationQuotient

/-!
# The explicit two-generator presentation sequence

The relation map has exactly the kernel of the quotient projection as its
image. Its kernel vanishes whenever either relation coefficient is a unit.
-/

@[expose] public noncomputable section

namespace FLT.Mazur.TwoGeneratorRelation

variable {C : Type*} [CommRing C] (x y : C)

/-- The map imposing the single relation y dx + x dy. -/
def relationMap : C →ₗ[C] C × C := (LinearMap.id (R := C)).smulRight (y, x)

/-- The relation map has its expected coordinate formula. -/
@[simp] theorem relationMap_apply (a : C) : relationMap x y a = (a * y, a * x) := rfl

/-- The image of the relation map is the relation submodule. -/
theorem range_relationMap : LinearMap.range (relationMap x y) = relations x y := by
  ext p
  change (∃ a, a • (y, x) = p) ↔ p ∈ Submodule.span C {(y, x)}
  exact Submodule.mem_span_singleton.symm

/-- The relation image is exactly the kernel of the cokernel projection. -/
theorem ker_projection :
    LinearMap.ker (relations x y).mkQ = LinearMap.range (relationMap x y) := by
  rw [Submodule.ker_mkQ, range_relationMap]

/-- A unit first coordinate makes the relation map injective. -/
theorem relationMap_injective_left (hx : IsUnit x) : Function.Injective (relationMap x y) := by
  intro a b hab
  have h := congrArg Prod.snd hab
  change a * x = b * x at h
  exact hx.mul_right_cancel h

/-- A unit second coordinate makes the relation map injective. -/
theorem relationMap_injective_right (hy : IsUnit y) :
    Function.Injective (relationMap x y) := by
  intro a b hab
  have h := congrArg Prod.fst hab
  change a * y = b * y at h
  exact hy.mul_right_cancel h

/-- Invertibility of the coordinate product kills the kernel of the relation map. -/
theorem ker_relationMap_of_isUnit_mul (hxy : IsUnit (x * y)) :
    LinearMap.ker (relationMap x y) = ⊥ :=
  LinearMap.ker_eq_bot.mpr (relationMap_injective_left x y (IsUnit.mul_iff.mp hxy).1)

end FLT.Mazur.TwoGeneratorRelation
