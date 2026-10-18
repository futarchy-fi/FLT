/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.OddWeierstrassCyclicHomGlobalMarkedRelation

/-!
# Identity, reversal and composition in the original subgroup relation

The maps are actual scheme morphisms of the normalization kernel pair. They
retain all original subgroup parameters and hence their global marked comparisons.
-/

@[expose] public noncomputable section
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
namespace FLT.Mazur.OddWeierstrassParameter
open UniversalWeierstrass (Labels)
variable (n : ℕ) [NeZero n]

/-- The identity relation at each original subgroup parameter. -/
def cyclicHomLocusRelationDiagonal :
    cyclicHomUniversalMultiplicationLocus n ⟶ cyclicHomLocusNormalizationRelation n :=
  cyclicHomLocusRelationPoint n (𝟙 _) (𝟙 _) rfl

/-- Identity retains the first original parameter. -/
@[reassoc] theorem cyclicHomLocusRelationDiagonal_first :
    cyclicHomLocusRelationDiagonal n ≫ cyclicHomLocusRelationFirst n = 𝟙 _ :=
  cyclicHomLocusRelationPoint_first n _ _ _

/-- Identity retains the second original parameter. -/
@[reassoc] theorem cyclicHomLocusRelationDiagonal_second :
    cyclicHomLocusRelationDiagonal n ≫ cyclicHomLocusRelationSecond n = 𝟙 _ :=
  cyclicHomLocusRelationPoint_second n _ _ _

/-- Reverse an actual pair of original subgroup presentations. -/
def cyclicHomLocusRelationSwap :
    cyclicHomLocusNormalizationRelation n ⟶ cyclicHomLocusNormalizationRelation n :=
  cyclicHomLocusRelationPoint n (cyclicHomLocusRelationSecond n)
    (cyclicHomLocusRelationFirst n) (cyclicHomLocusRelation_condition n).symm

/-- Reversal retains the original second parameter as its first. -/
@[reassoc] theorem cyclicHomLocusRelationSwap_first :
    cyclicHomLocusRelationSwap n ≫ cyclicHomLocusRelationFirst n =
      cyclicHomLocusRelationSecond n := cyclicHomLocusRelationPoint_first n _ _ _

/-- Reversal retains the original first parameter as its second. -/
@[reassoc] theorem cyclicHomLocusRelationSwap_second :
    cyclicHomLocusRelationSwap n ≫ cyclicHomLocusRelationSecond n =
      cyclicHomLocusRelationFirst n := cyclicHomLocusRelationPoint_second n _ _ _

/-- Reversing the relation twice is the identity scheme morphism. -/
theorem cyclicHomLocusRelationSwap_involutive :
    cyclicHomLocusRelationSwap n ≫ cyclicHomLocusRelationSwap n = 𝟙 _ := by
  apply cyclicHomLocusRelation_hom_ext
  · simp only [Category.assoc, cyclicHomLocusRelationSwap_first,
      cyclicHomLocusRelationSwap_second, Category.id_comp]
  · simp only [Category.assoc, cyclicHomLocusRelationSwap_second,
      cyclicHomLocusRelationSwap_first, Category.id_comp]

/-- The scheme of composable original subgroup comparisons. -/
def cyclicHomLocusRelationComposable : Scheme :=
  pullback (cyclicHomLocusRelationSecond n) (cyclicHomLocusRelationFirst n)

/-- Composable original comparisons have equal normalized outer parameters. -/
theorem cyclicHomLocusRelation_outer_eq :
    (pullback.fst (cyclicHomLocusRelationSecond n) (cyclicHomLocusRelationFirst n) ≫
      cyclicHomLocusRelationFirst n) ≫ cyclicHomLocusNormalization n =
    (pullback.snd (cyclicHomLocusRelationSecond n) (cyclicHomLocusRelationFirst n) ≫
      cyclicHomLocusRelationSecond n) ≫ cyclicHomLocusNormalization n := by
  rw [Category.assoc, cyclicHomLocusRelation_condition, ← Category.assoc,
    pullback.condition, Category.assoc, cyclicHomLocusRelation_condition, ← Category.assoc]

/-- Composition retains precisely the two outer original subgroup parameters. -/
def cyclicHomLocusRelationCompose :
    cyclicHomLocusRelationComposable n ⟶ cyclicHomLocusNormalizationRelation n :=
  cyclicHomLocusRelationPoint n
    (pullback.fst _ _ ≫ cyclicHomLocusRelationFirst n)
    (pullback.snd _ _ ≫ cyclicHomLocusRelationSecond n) (cyclicHomLocusRelation_outer_eq n)

/-- The source of a composite is the first original source. -/
@[reassoc] theorem cyclicHomLocusRelationCompose_first :
    cyclicHomLocusRelationCompose n ≫ cyclicHomLocusRelationFirst n =
      pullback.fst _ _ ≫ cyclicHomLocusRelationFirst n :=
  cyclicHomLocusRelationPoint_first n _ _ _

/-- The target of a composite is the last original target. -/
@[reassoc] theorem cyclicHomLocusRelationCompose_second :
    cyclicHomLocusRelationCompose n ≫ cyclicHomLocusRelationSecond n =
      pullback.snd _ _ ≫ cyclicHomLocusRelationSecond n :=
  cyclicHomLocusRelationPoint_second n _ _ _

end FLT.Mazur.OddWeierstrassParameter
