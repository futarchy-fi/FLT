/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.CyclicCharacteristicUnmarkedSheafRelation
public import FLT.Mazur.CyclicCharacteristicTransitionSpan
public import Mathlib.CategoryTheory.Sites.Subcanonical

/-!
# Actual scheme tests of the full unmarked sheaf relation

Every pair of locally compatible normalized parameters gives a canonical
test of the full relation with both prescribed source arms. In particular,
the previously constructed cross-characteristic scheme spans map into it.
This connects the concrete transition geometry with the exact sheaf kernel.
-/

@[expose] public noncomputable section
open CategoryTheory Limits AlgebraicGeometry
namespace FLT.Mazur.CyclicCharacteristicAtlas
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
variable (n : ℕ) [NeZero n] {T : Scheme}

/-- An original parameter viewed as a test of the actual represented disjoint source. -/
def unmarkedSourceTest (q : NormalizedParameter n T) :
    Scheme.fppfTopology.uliftYoneda.{1}.obj T ⟶
      Scheme.fppfTopology.uliftYoneda.{1}.obj (normalizedDisjointSource n) :=
  Scheme.fppfTopology.uliftYoneda.map (q.2.down ≫ normalizedDisjointInclusion n q.1)

/-- Two actual scheme tests have equal quotient maps exactly for local full comparison. -/
theorem unmarkedSourceTest_eq_iff (q r : NormalizedParameter n T) :
    unmarkedSourceTest n q ≫ unmarkedDisjointSourceMap n =
      unmarkedSourceTest n r ≫ unmarkedDisjointSourceMap n ↔
        LocallyUnmarkedRelated n q r := by
  rw [← unmarkedSourceRelation_parameter_iff]
  constructor
  · intro h
    have he := congrArg (fun a ↦ a.hom.app (Opposite.op T) (ULift.up (𝟙 T))) h
    change (unmarkedDisjointSourceMap n).hom.app (Opposite.op T)
        (ULift.up (𝟙 T ≫ q.2.down ≫ normalizedDisjointInclusion n q.1)) =
      (unmarkedDisjointSourceMap n).hom.app (Opposite.op T)
        (ULift.up (𝟙 T ≫ r.2.down ≫ normalizedDisjointInclusion n r.1)) at he
    simpa only [Category.id_comp] using he
  · intro h
    apply Scheme.fppfTopology.uliftYonedaEquiv.injective
    change (unmarkedDisjointSourceMap n).hom.app (Opposite.op T)
        (ULift.up (𝟙 T ≫ q.2.down ≫ normalizedDisjointInclusion n q.1)) =
      (unmarkedDisjointSourceMap n).hom.app (Opposite.op T)
        (ULift.up (𝟙 T ≫ r.2.down ≫ normalizedDisjointInclusion n r.1))
    simpa only [Category.id_comp] using h

/-- Local full comparisons give actual tests of the constructed entire relation. -/
def unmarkedRelationTest (q r : NormalizedParameter n T)
    (h : LocallyUnmarkedRelated n q r) :
    Scheme.fppfTopology.uliftYoneda.{1}.obj T ⟶ unmarkedSourceRelationSheaf n :=
  pullback.lift (unmarkedSourceTest n q) (unmarkedSourceTest n r)
    ((unmarkedSourceTest_eq_iff n q r).mpr h)

/-- The first relation arm is the prescribed original parameter test. -/
@[reassoc] theorem unmarkedRelationTest_fst (q r : NormalizedParameter n T)
    (h : LocallyUnmarkedRelated n q r) :
    unmarkedRelationTest n q r h ≫ unmarkedSourceRelationFst n = unmarkedSourceTest n q :=
  pullback.lift_fst _ _ _

/-- The second relation arm is the prescribed comparison parameter test. -/
@[reassoc] theorem unmarkedRelationTest_snd (q r : NormalizedParameter n T)
    (h : LocallyUnmarkedRelated n q r) :
    unmarkedRelationTest n q r h ≫ unmarkedSourceRelationSnd n = unmarkedSourceTest n r :=
  pullback.lift_snd _ _ _

/-- Each existing cross-characteristic scheme span is a test of the full unmarked relation. -/
def transitionUnmarkedRelationTest (b : Bool) (i : (transitionCover n b).I₀) :
    Scheme.fppfTopology.uliftYoneda.{1}.obj ((transitionCover n b).X i) ⟶
      unmarkedSourceRelationSheaf n :=
  unmarkedRelationTest n ⟨!b, ULift.up (transitionTarget n b i)⟩
    ⟨b, ULift.up (transitionSource n b i)⟩
    (locallyUnmarkedRelated_of_related n (transition_unmarkedRelated n b i))

end FLT.Mazur.CyclicCharacteristicAtlas
