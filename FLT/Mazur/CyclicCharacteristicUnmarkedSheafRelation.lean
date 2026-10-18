/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.CyclicCharacteristicUnmarkedSourceSheaf
public import FLT.Mazur.CyclicCharacteristicUnmarkedLocalRelation

/-!
# The full relation of the actual source in fppf sheaves

The kernel pair of the actual represented source is constructed in sheaves.
Its coequalizer is the unmarked sheaf quotient. On every pair of original
chart tests its kernel is exactly local compatible comparison, including
cross-characteristic comparisons and arbitrary Cartier generator changes.
Representing this relation by a scheme remains a geometric construction.
-/

@[expose] public noncomputable section
open CategoryTheory Limits AlgebraicGeometry
namespace FLT.Mazur.CyclicCharacteristicAtlas
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
variable (n : ℕ) [NeZero n]

/-- The full kernel-pair relation of the original represented disjoint source. -/
def unmarkedSourceRelationSheaf : Sheaf Scheme.fppfTopology (Type 1) :=
  pullback (unmarkedDisjointSourceMap n) (unmarkedDisjointSourceMap n)

/-- The first projection retains the actual disjoint scheme source. -/
def unmarkedSourceRelationFst : unmarkedSourceRelationSheaf n ⟶
    Scheme.fppfTopology.uliftYoneda.{1}.obj (normalizedDisjointSource n) :=
  pullback.fst _ _

/-- The second projection retains the same actual disjoint scheme source. -/
def unmarkedSourceRelationSnd : unmarkedSourceRelationSheaf n ⟶
    Scheme.fppfTopology.uliftYoneda.{1}.obj (normalizedDisjointSource n) :=
  pullback.snd _ _

/-- Both full relation projections have the same actual quotient class. -/
theorem unmarkedSourceRelation_condition :
    unmarkedSourceRelationFst n ≫ unmarkedDisjointSourceMap n =
      unmarkedSourceRelationSnd n ≫ unmarkedDisjointSourceMap n := pullback.condition

/-- The original unmarked quotient is the vertex of the full source relation cofork. -/
def unmarkedSourceRelationCofork :
    Cofork (unmarkedSourceRelationFst n) (unmarkedSourceRelationSnd n) :=
  Cofork.ofπ (unmarkedDisjointSourceMap n) (unmarkedSourceRelation_condition n)

/-- The full unmarked quotient is the coequalizer of its actual source relation in sheaves. -/
def unmarkedSourceRelationIsColimit : IsColimit (unmarkedSourceRelationCofork n) :=
  isColimitCoforkOfEffectiveEpi (unmarkedDisjointSourceMap n) _ (pullback.isLimit _ _)

/-- An actual source test retains its original fixed-chart unmarked parameter class. -/
theorem unmarkedDisjointSourceMap_parameter {T : Scheme} (q : NormalizedParameter n T) :
    (unmarkedDisjointSourceMap n).hom.app (Opposite.op T)
      (ULift.up (q.2.down ≫ normalizedDisjointInclusion n q.1)) =
        (unmarkedParameterSheafMap n).app (Opposite.op T) q :=
  congrArg (fun a ↦ a.app (Opposite.op T) q) (parameterToDisjointSource_unmarked n)

/-- The full source relation on actual chart tests is exactly local compatible isomorphism. -/
theorem unmarkedSourceRelation_parameter_iff {T : Scheme} (q r : NormalizedParameter n T) :
    (unmarkedDisjointSourceMap n).hom.app (Opposite.op T)
        (ULift.up (q.2.down ≫ normalizedDisjointInclusion n q.1)) =
      (unmarkedDisjointSourceMap n).hom.app (Opposite.op T)
        (ULift.up (r.2.down ≫ normalizedDisjointInclusion n r.1)) ↔
      LocallyUnmarkedRelated n q r := by
  rw [unmarkedDisjointSourceMap_parameter, unmarkedDisjointSourceMap_parameter]
  exact unmarkedParameterSheafMap_eq_iff n q r

end FLT.Mazur.CyclicCharacteristicAtlas
