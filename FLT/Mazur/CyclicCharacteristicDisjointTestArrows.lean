/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.CyclicCharacteristicDisjointInverseDiagrams

/-!
# Specified global comparison arrows on scheme tests

The morphisms between two tests of the normalized base are actual maps to the
assembled arrow scheme with those endpoints. Operations use the scheme maps.
-/

@[expose] public noncomputable section
open CategoryTheory Limits AlgebraicGeometry
namespace FLT.Mazur.CyclicCharacteristicAtlas
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
variable (n : ℕ) [NeZero n] {T : Scheme}
local notation "src" => disjointComparisonSource n
local notation "tgt" => disjointComparisonTarget n

/-- All actual global parameters with specified endpoints, retaining stabilizers. -/
abbrev DisjointArrow (q r : T ⟶ normalizedDisjointSource n) :=
  {a : T ⟶ disjointComparisonArrows n // a ≫ src = q ∧ a ≫ tgt = r}

/-- Identity of a global base test, induced by the identity scheme map. -/
def disjointArrowId (q : T ⟶ normalizedDisjointSource n) : DisjointArrow n q q :=
  ⟨q ≫ disjointComparisonIdentity n, by
    simp only [Category.assoc, disjointComparisonIdentity_source,
      disjointComparisonIdentity_target, Category.comp_id, and_self]⟩

/-- Inverse of a specified global arrow, induced by the inversion scheme map. -/
def disjointArrowInv {q r : T ⟶ normalizedDisjointSource n}
    (a : DisjointArrow n q r) : DisjointArrow n r q :=
  ⟨a.val ≫ disjointComparisonInverse n, by
    simpa only [Category.assoc, disjointComparisonInverse_source,
      disjointComparisonInverse_target] using And.intro a.property.2 a.property.1⟩

/-- Composite of specified global arrows, induced by the composition scheme map. -/
def disjointArrowComp {q r s : T ⟶ normalizedDisjointSource n}
    (a : DisjointArrow n q r) (z : DisjointArrow n r s) : DisjointArrow n q s :=
  ⟨disjointComposableLift n a.val z.val (a.property.2.trans z.property.1.symm) ≫
    disjointCompositionMap n, by
      simp only [Category.assoc, disjointCompositionMap_source, disjointCompositionMap_target,
        disjointComposableLift_first_assoc, disjointComposableLift_second_assoc]
      exact ⟨a.property.1, z.property.2⟩⟩

/-- The identity scheme diagram implies the left identity law on every scheme test. -/
theorem disjointArrowId_comp {q r : T ⟶ normalizedDisjointSource n}
    (a : DisjointArrow n q r) : disjointArrowComp n (disjointArrowId n q) a = a := by
  apply Subtype.ext
  have h : disjointComposableLift n (disjointArrowId n q).val a.val
      ((disjointArrowId n q).property.2.trans a.property.1.symm) =
        a.val ≫ disjointLeftUnitInsertion n := by
    apply pullback.hom_ext
    · simp only [disjointLeftUnitInsertion, Category.assoc, disjointComposableLift_first]
      change q ≫ disjointComparisonIdentity n = a.val ≫ src ≫ disjointComparisonIdentity n
      rw [← Category.assoc, a.property.1]
    · simp only [disjointLeftUnitInsertion, Category.assoc, disjointComposableLift_second,
        Category.comp_id]
  change _ ≫ disjointCompositionMap n = a.val
  rw [h, Category.assoc, disjointCompositionMap_left_unit, Category.comp_id]

/-- The identity scheme diagram implies the right identity law on every scheme test. -/
theorem disjointArrowComp_id {q r : T ⟶ normalizedDisjointSource n}
    (a : DisjointArrow n q r) : disjointArrowComp n a (disjointArrowId n r) = a := by
  apply Subtype.ext
  have h : disjointComposableLift n a.val (disjointArrowId n r).val
      (a.property.2.trans (disjointArrowId n r).property.1.symm) =
        a.val ≫ disjointRightUnitInsertion n := by
    apply pullback.hom_ext
    · simp only [disjointRightUnitInsertion, Category.assoc, disjointComposableLift_first,
        Category.comp_id]
    · simp only [disjointRightUnitInsertion, Category.assoc, disjointComposableLift_second]
      change r ≫ disjointComparisonIdentity n = a.val ≫ tgt ≫ disjointComparisonIdentity n
      rw [← Category.assoc, a.property.2]
  change _ ≫ disjointCompositionMap n = a.val
  rw [h, Category.assoc, disjointCompositionMap_right_unit, Category.comp_id]

/-- The inverse scheme diagram implies the right inverse law on every scheme test. -/
theorem disjointArrowComp_inv {q r : T ⟶ normalizedDisjointSource n}
    (a : DisjointArrow n q r) :
    disjointArrowComp n a (disjointArrowInv n a) = disjointArrowId n q := by
  apply Subtype.ext
  have h : disjointComposableLift n a.val (disjointArrowInv n a).val
      (a.property.2.trans (disjointArrowInv n a).property.1.symm) =
        a.val ≫ disjointRightInverseInsertion n := by
    apply pullback.hom_ext <;>
      simp only [disjointRightInverseInsertion, Category.assoc, disjointComposableLift_first,
        disjointComposableLift_second, Category.comp_id]
    rfl
  change _ ≫ disjointCompositionMap n = q ≫ disjointComparisonIdentity n
  rw [h, Category.assoc, disjointCompositionMap_right_inverse, ← Category.assoc, a.property.1]

/-- The inverse scheme diagram implies the left inverse law on every scheme test. -/
theorem disjointArrowInv_comp {q r : T ⟶ normalizedDisjointSource n}
    (a : DisjointArrow n q r) :
    disjointArrowComp n (disjointArrowInv n a) a = disjointArrowId n r := by
  apply Subtype.ext
  have h : disjointComposableLift n (disjointArrowInv n a).val a.val
      ((disjointArrowInv n a).property.2.trans a.property.1.symm) =
        a.val ≫ disjointLeftInverseInsertion n := by
    apply pullback.hom_ext <;>
      simp only [disjointLeftInverseInsertion, Category.assoc, disjointComposableLift_first,
        disjointComposableLift_second, Category.comp_id]
    rfl
  change _ ≫ disjointCompositionMap n = r ≫ disjointComparisonIdentity n
  rw [h, Category.assoc, disjointCompositionMap_left_inverse, ← Category.assoc, a.property.2]

end FLT.Mazur.CyclicCharacteristicAtlas
