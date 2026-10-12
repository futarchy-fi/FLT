/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.ClosedGroupIdealOperations

/-!
# A group structure from the actual ideal equations

All group identities follow by cancellation of the original closed immersion.
Conversely, an actual group with that closed immersion satisfies the equations.
-/

@[expose] public noncomputable section
open CategoryTheory Limits AlgebraicGeometry MonoidalCategory MonObj GrpObj
universe u
namespace FLT.Mazur.ClosedGroupIdeal
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
variable {S : Scheme.{u}} (G : Over S) [CommGrpObj G] (I : G.left.IdealSheafData)
  (hu : unitEquation G I = 0) (hm : multiplicationEquation G I = 0)
  (hi : inverseEquation G I = 0)

/-- The zero equations construct the group laws on the full closed subscheme. -/
@[instance_reducible] def commGrpObj : CommGrpObj (carrier G I) :=
  CartesianMonoGroup.commGrpObj (inclusion G I) (unit G I hu) (multiplication G I hm)
    (inverse G I hi) (unit_inclusion G I hu) (multiplication_inclusion G I hm)
    (inverse_inclusion G I hi)

/-- The constructed group retains its original closed immersion as a group morphism. -/
instance inclusion_isMonHom :
    letI := commGrpObj G I hu hm hi
    IsMonHom (inclusion G I) := by
  let _ := commGrpObj G I hu hm hi
  exact ⟨unit_inclusion G I hu, multiplication_inclusion G I hm⟩

/-- The group scheme defined by the vanishing equations. -/
def group : CommGrp (Over S) := by
  letI := commGrpObj G I hu hm hi
  exact ⟨carrier G I⟩

variable {H : Over S} [CommGrpObj H] (j : H ⟶ G) [IsMonHom j]
  (e : H ≅ carrier G I) (he : e.hom ≫ inclusion G I = j)

include he in
/-- An actual subgroup with this carrier satisfies the unit equation. -/
theorem unitEquation_of_group : unitEquation G I = 0 := by
  apply (vanishing_iff_lift G I η[G]).mpr
  refine ⟨η[H] ≫ e.hom, ?_⟩
  rw [Category.assoc, he, IsMonHom.one_hom]

include he in
/-- An actual subgroup with this carrier satisfies the entire multiplication equation. -/
theorem multiplicationEquation_of_group : multiplicationEquation G I = 0 := by
  apply (vanishing_iff_lift G I (productMap G I)).mpr
  refine ⟨(e.inv ⊗ₘ e.inv) ≫ μ[H] ≫ e.hom, ?_⟩
  have hj : e.inv ≫ j = inclusion G I := by rw [← he, e.inv_hom_id_assoc]
  rw [Category.assoc, Category.assoc, he, IsMonHom.mul_hom,
    ← Category.assoc, tensorHom_comp_tensorHom, hj]
  rfl

include he in
/-- An actual subgroup with this carrier satisfies the inverse equation. -/
theorem inverseEquation_of_group : inverseEquation G I = 0 := by
  apply (vanishing_iff_lift G I (inclusion G I ≫ ι[G])).mpr
  refine ⟨e.inv ≫ ι[H] ≫ e.hom, ?_⟩
  have hj : e.inv ≫ j = inclusion G I := by rw [← he, e.inv_hom_id_assoc]
  rw [Category.assoc, Category.assoc, he, GrpObj.inv_hom, ← Category.assoc, hj]

end FLT.Mazur.ClosedGroupIdeal
