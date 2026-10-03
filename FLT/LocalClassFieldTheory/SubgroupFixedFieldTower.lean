/-
Copyright (c) 2026 krandder. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: krandder
-/
module

public import Mathlib.FieldTheory.Galois.Basic

/-!
# The field tower belonging to an arbitrary subgroup

Place the fixed field inside the original ambient field and identify its Galois
group with the given subgroup. Restriction of scalars is exactly subgroup inclusion.
-/

@[expose] public noncomputable section

set_option backward.isDefEq.respectTransparency false

namespace LocalClassFieldTheory

variable {K C : Type} [Field K] [Field C] [Algebra K C]
  (F : IntermediateField K C) [FiniteDimensional K F] (H : Subgroup Gal(F/K))

/-- The subgroup's fixed field, viewed inside the ambient field. -/
def subgroupFixedField : IntermediateField K C :=
  IntermediateField.lift (IntermediateField.fixedField H)

omit [FiniteDimensional K F] in
/-- The fixed field lies below the original finite extension. -/
theorem subgroupFixedField_le : subgroupFixedField F H ≤ F :=
  IntermediateField.lift_le _

/-- The original field, now considered over the subgroup's fixed field. -/
def subgroupTopField : IntermediateField (subgroupFixedField F H) C :=
  IntermediateField.extendScalars (subgroupFixedField_le F H)

omit [FiniteDimensional K F] in
/-- Returning to the original base gives the original intermediate field. -/
theorem subgroupTopField_restrictScalars : (subgroupTopField F H).restrictScalars K = F := rfl

/-- The actual fixed-field Galois identification for an arbitrary subgroup. -/
def subgroupFixedFieldEquiv : H ≃* Gal(subgroupTopField F H / subgroupFixedField F H) where
  toFun σ :=
    { (σ.val : Gal(F/K)).toRingEquiv with
      commutes' := fun x => by
        apply Subtype.ext
        obtain ⟨y, hy, he⟩ := x.property
        change (σ.val (⟨x.val, subgroupFixedField_le F H x.property⟩ : F)).val = x.val
        have hfix : σ.val y = y := hy σ
        have hyx : (⟨x.val, subgroupFixedField_le F H x.property⟩ : F) = y :=
          Subtype.ext he.symm
        rw [hyx]
        exact (congrArg Subtype.val hfix).trans he }
  invFun σ := ⟨σ.restrictScalars K, by
    apply (show (IntermediateField.fixedField H).fixingSubgroup ≤ H from
      le_of_eq (IntermediateField.fixingSubgroup_fixedField H))
    intro x
    have hc := σ.commutes (IntermediateField.liftAlgEquiv (IntermediateField.fixedField H) x)
    exact hc⟩
  left_inv σ := by apply Subtype.ext; rfl
  right_inv σ := by ext x; rfl
  map_mul' _ _ := by ext x; rfl

/-- The Galois identification intertwines restriction of scalars with subgroup inclusion. -/
theorem subgroupFixedFieldEquiv_restrictScalars :
    (AlgEquiv.restrictScalarsHom K).comp (subgroupFixedFieldEquiv F H).toMonoidHom =
      H.subtype := by
  ext σ x
  rfl

end LocalClassFieldTheory
