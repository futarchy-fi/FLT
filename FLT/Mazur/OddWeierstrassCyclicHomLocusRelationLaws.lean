/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.OddWeierstrassCyclicHomLocusRelationGroupoid

/-!
# Composition laws for points of the actual subgroup relation

Composition of scheme-valued relation points satisfies the groupoid laws.
Every equality follows from the two retained original subgroup projections.
-/

@[expose] public noncomputable section
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
namespace FLT.Mazur.OddWeierstrassParameter
open UniversalWeierstrass (Labels)
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
variable (n : ℕ) [NeZero n] {T : Scheme}

/-- Compose actual relation points with a common original middle parameter. -/
def cyclicHomLocusRelationPointComp
    (a b : T ⟶ cyclicHomLocusNormalizationRelation n)
    (h : a ≫ cyclicHomLocusRelationSecond n = b ≫ cyclicHomLocusRelationFirst n) :
    T ⟶ cyclicHomLocusNormalizationRelation n :=
  pullback.lift a b h ≫ cyclicHomLocusRelationCompose n

/-- Composition retains its original source point. -/
@[reassoc] theorem cyclicHomLocusRelationPointComp_first
    (a b : T ⟶ cyclicHomLocusNormalizationRelation n)
    (h : a ≫ cyclicHomLocusRelationSecond n = b ≫ cyclicHomLocusRelationFirst n) :
    cyclicHomLocusRelationPointComp n a b h ≫ cyclicHomLocusRelationFirst n =
      a ≫ cyclicHomLocusRelationFirst n := by
  simp only [cyclicHomLocusRelationPointComp, Category.assoc,
    cyclicHomLocusRelationCompose_first, pullback.lift_fst_assoc]

/-- Composition retains its original target point. -/
@[reassoc] theorem cyclicHomLocusRelationPointComp_second
    (a b : T ⟶ cyclicHomLocusNormalizationRelation n)
    (h : a ≫ cyclicHomLocusRelationSecond n = b ≫ cyclicHomLocusRelationFirst n) :
    cyclicHomLocusRelationPointComp n a b h ≫ cyclicHomLocusRelationSecond n =
      b ≫ cyclicHomLocusRelationSecond n := by
  simp only [cyclicHomLocusRelationPointComp, Category.assoc,
    cyclicHomLocusRelationCompose_second, pullback.lift_snd_assoc]

/-- The identity at the original source acts as a left unit. -/
theorem cyclicHomLocusRelationPointComp_left_id
    (a : T ⟶ cyclicHomLocusNormalizationRelation n)
    (h : (a ≫ cyclicHomLocusRelationFirst n ≫ cyclicHomLocusRelationDiagonal n) ≫
      cyclicHomLocusRelationSecond n = a ≫ cyclicHomLocusRelationFirst n) :
    cyclicHomLocusRelationPointComp n
      (a ≫ cyclicHomLocusRelationFirst n ≫ cyclicHomLocusRelationDiagonal n) a h = a := by
  apply cyclicHomLocusRelation_hom_ext
  · simp only [cyclicHomLocusRelationPointComp_first, Category.assoc,
      cyclicHomLocusRelationDiagonal_first, Category.comp_id]
  · exact cyclicHomLocusRelationPointComp_second n _ _ _

/-- The identity at the original target acts as a right unit. -/
theorem cyclicHomLocusRelationPointComp_right_id
    (a : T ⟶ cyclicHomLocusNormalizationRelation n)
    (h : a ≫ cyclicHomLocusRelationSecond n =
      (a ≫ cyclicHomLocusRelationSecond n ≫ cyclicHomLocusRelationDiagonal n) ≫
        cyclicHomLocusRelationFirst n) :
    cyclicHomLocusRelationPointComp n a
      (a ≫ cyclicHomLocusRelationSecond n ≫ cyclicHomLocusRelationDiagonal n) h = a := by
  apply cyclicHomLocusRelation_hom_ext
  · exact cyclicHomLocusRelationPointComp_first n _ _ _
  · simp only [cyclicHomLocusRelationPointComp_second, Category.assoc,
      cyclicHomLocusRelationDiagonal_second, Category.comp_id]

/-- Composition is associative on all actual scheme-valued relation points. -/
theorem cyclicHomLocusRelationPointComp_assoc
    (a b c : T ⟶ cyclicHomLocusNormalizationRelation n)
    (hab : a ≫ cyclicHomLocusRelationSecond n = b ≫ cyclicHomLocusRelationFirst n)
    (hbc : b ≫ cyclicHomLocusRelationSecond n = c ≫ cyclicHomLocusRelationFirst n)
    (hl : cyclicHomLocusRelationPointComp n a b hab ≫ cyclicHomLocusRelationSecond n =
      c ≫ cyclicHomLocusRelationFirst n)
    (hr : a ≫ cyclicHomLocusRelationSecond n =
      cyclicHomLocusRelationPointComp n b c hbc ≫ cyclicHomLocusRelationFirst n) :
    cyclicHomLocusRelationPointComp n (cyclicHomLocusRelationPointComp n a b hab) c hl =
      cyclicHomLocusRelationPointComp n a (cyclicHomLocusRelationPointComp n b c hbc) hr := by
  apply cyclicHomLocusRelation_hom_ext
  · simp only [cyclicHomLocusRelationPointComp_first]
  · simp only [cyclicHomLocusRelationPointComp_second]

/-- A relation point followed by its reversal is the original source identity. -/
theorem cyclicHomLocusRelationPointComp_inverse
    (a : T ⟶ cyclicHomLocusNormalizationRelation n)
    (h : a ≫ cyclicHomLocusRelationSecond n =
      (a ≫ cyclicHomLocusRelationSwap n) ≫ cyclicHomLocusRelationFirst n) :
    cyclicHomLocusRelationPointComp n a (a ≫ cyclicHomLocusRelationSwap n) h =
      a ≫ cyclicHomLocusRelationFirst n ≫ cyclicHomLocusRelationDiagonal n := by
  apply cyclicHomLocusRelation_hom_ext
  · simp only [cyclicHomLocusRelationPointComp_first, Category.assoc,
      cyclicHomLocusRelationDiagonal_first, Category.comp_id]
  · simp only [cyclicHomLocusRelationPointComp_second, Category.assoc,
      cyclicHomLocusRelationSwap_second, cyclicHomLocusRelationDiagonal_second, Category.comp_id]

end FLT.Mazur.OddWeierstrassParameter
