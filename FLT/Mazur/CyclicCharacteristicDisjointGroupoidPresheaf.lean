/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.CyclicCharacteristicDisjointTestGroupoid
public import Mathlib.CategoryTheory.Groupoid.Grpd.Basic

/-!
# The represented comparison groupoid as a presheaf

The global scheme operations assemble into a groupoid-valued presheaf on all
schemes. Its object presheaf is represented by the normalized disjoint atlas;
its specified arrows remain maps to the assembled comparison scheme.
-/

@[expose] public noncomputable section
open CategoryTheory Limits AlgebraicGeometry
namespace FLT.Mazur.CyclicCharacteristicAtlas
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
variable (n : ℕ) [NeZero n]

/-- Restriction along the identity is the identity functor on the test groupoid. -/
theorem disjointTestRestriction_id (T : Scheme) :
    disjointTestRestriction n (𝟙 T) = 𝟭 (DisjointTestObject n T) := by
  apply Functor.hext
  · intro q
    exact Category.id_comp q
  · intro q r a
    change HEq (disjointArrowRestrict n (𝟙 T) a) a
    apply (Subtype.heq_iff_coe_eq (fun k ↦ ?_)).mpr (Category.id_comp a.val)
    change (k ≫ disjointComparisonSource n = 𝟙 T ≫ q ∧
      k ≫ disjointComparisonTarget n = 𝟙 T ≫ r) ↔
      (k ≫ disjointComparisonSource n = q ∧ k ≫ disjointComparisonTarget n = r)
    simp only [Category.id_comp]

/-- Restriction along a composite is the composite of the two restriction functors. -/
theorem disjointTestRestriction_comp {T U V : Scheme} (f : U ⟶ T) (g : V ⟶ U) :
    disjointTestRestriction n (g ≫ f) =
      disjointTestRestriction n f ⋙ disjointTestRestriction n g := by
  apply Functor.hext
  · intro q
    exact Category.assoc g f q
  · intro q r a
    change HEq (disjointArrowRestrict n (g ≫ f) a)
      (disjointArrowRestrict n g (disjointArrowRestrict n f a))
    apply (Subtype.heq_iff_coe_eq (fun k ↦ ?_)).mpr (Category.assoc g f a.val)
    simp only [Category.assoc]

/-- The internal comparison groupoid evaluated functorially on every scheme. -/
def disjointGroupoidPresheaf : Schemeᵒᵖ ⥤ Grpd where
  obj T := Grpd.of (DisjointTestObject n T.unop)
  map f := disjointTestRestriction n f.unop
  map_id T := disjointTestRestriction_id n T.unop
  map_comp f g := disjointTestRestriction_comp n f.unop g.unop

/-- The objects of the groupoid presheaf are represented by the original normalized atlas. -/
theorem disjointGroupoidPresheaf_objects :
    disjointGroupoidPresheaf n ⋙ Grpd.objects = yoneda.obj (normalizedDisjointSource n) := rfl

end FLT.Mazur.CyclicCharacteristicAtlas
