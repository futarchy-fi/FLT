/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.CyclicCharacteristicDisjointTestAssociativity
public import Mathlib.CategoryTheory.Groupoid

/-!
# The groupoid of normalized atlas tests

For every scheme, maps to the normalized atlas form a groupoid whose arrows
are all specified maps to the comparison scheme. Every law is derived from
the constructed scheme diagrams, including for disconnected scheme tests.
-/

@[expose] public noncomputable section
open CategoryTheory Limits AlgebraicGeometry
namespace FLT.Mazur.CyclicCharacteristicAtlas
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
variable (n : ℕ) [NeZero n]

/-- Objects of the represented comparison groupoid on a scheme test. -/
def DisjointTestObject (T : Scheme) := T ⟶ normalizedDisjointSource n

/-- The actual global scheme operations give a groupoid on every scheme test. -/
instance disjointTestGroupoid (T : Scheme) : Groupoid (DisjointTestObject n T) where
  Hom q r := DisjointArrow n q r
  id q := disjointArrowId n q
  comp a z := disjointArrowComp n a z
  id_comp a := disjointArrowId_comp n a
  comp_id a := disjointArrowComp_id n a
  assoc a z w := disjointArrowComp_assoc n a z w
  inv a := disjointArrowInv n a
  inv_comp a := disjointArrowInv_comp n a
  comp_inv a := disjointArrowComp_inv n a

/-- Restriction of a specified global arrow keeps its map and both endpoints. -/
def disjointArrowRestrict {T U : Scheme} (f : U ⟶ T)
    {q r : T ⟶ normalizedDisjointSource n} (a : DisjointArrow n q r) :
    DisjointArrow n (f ≫ q) (f ≫ r) :=
  ⟨f ≫ a.val, by simp only [Category.assoc, a.property.1, a.property.2, and_self]⟩

/-- The represented groupoid restriction is a functor for every scheme morphism. -/
def disjointTestRestriction {T U : Scheme} (f : U ⟶ T) :
    DisjointTestObject n T ⥤ DisjointTestObject n U where
  obj q := f ≫ q
  map a := disjointArrowRestrict n f a
  map_id q := by
    apply Subtype.ext
    exact (Category.assoc f q (disjointComparisonIdentity n)).symm
  map_comp a z := by
    apply Subtype.ext
    change f ≫ disjointComposableLift n a.val z.val _ ≫ disjointCompositionMap n =
      disjointComposableLift n (f ≫ a.val) (f ≫ z.val) _ ≫ disjointCompositionMap n
    rw [← Category.assoc, disjointComposableLift_precomp]

/-- Identity restriction leaves each original specified arrow unchanged. -/
theorem disjointArrowRestrict_id {T : Scheme} {q r : T ⟶ normalizedDisjointSource n}
    (a : DisjointArrow n q r) : (disjointArrowRestrict n (𝟙 T) a).val = a.val :=
  Category.id_comp _

/-- Successive restrictions keep the same actual parameter as composite restriction. -/
theorem disjointArrowRestrict_comp {T U V : Scheme} (f : U ⟶ T) (g : V ⟶ U)
    {q r : T ⟶ normalizedDisjointSource n} (a : DisjointArrow n q r) :
    (disjointArrowRestrict n g (disjointArrowRestrict n f a)).val =
      (disjointArrowRestrict n (g ≫ f) a).val := (Category.assoc _ _ _).symm

end FLT.Mazur.CyclicCharacteristicAtlas
