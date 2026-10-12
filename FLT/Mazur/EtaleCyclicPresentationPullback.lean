/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.EtaleCyclicSubgroupLocalPresentation

/-!
# Local cyclic presentations retain the original subgroup under base change

The constructed constant-group map and curve marking commute with arbitrary
source change. For etale subgroups this identifies the actual split isomorphism
with its pullback, retaining every original generator power.
-/

@[expose] public noncomputable section
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry MonoidalCategory MonObj
open scoped CategoryTheory.Obj
namespace FLT.Mazur.GeneralizedEllipticCurve.FiniteSubgroup
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
variable {S T : Scheme} {E : GeneralizedEllipticCurve S} {n : ℕ} [NeZero n]
  (H : E.FiniteSubgroup n) {P : 𝟙_ (Over S) ⟶ H.carrier}
  (hP : H.IsCartierGenerator P) (g : T ⟶ S)

/-- The cyclic map of the pulled-back generator is the actual pullback of the original map. -/
theorem generatorCyclicMap_pullback :
    (H.baseChange g).generatorCyclicMap (H.pullGenerator g P) (hP.baseChange H g).1 =
      (ConstantCyclicPullback.equivalence g n).hom ≫
        (Over.pullback g).map (H.generatorCyclicMap P hP.1) := by
  apply Sigma.hom_ext
  intro i
  change ConstantCyclicGroup.component T n i ≫
    ConstantCyclicSectionMap.toScheme _ =
      ConstantCyclicGroup.component T n i ≫
        (ConstantCyclicPullback.equivalence g n).hom ≫
          (Over.pullback g).map (ConstantCyclicSectionMap.toScheme _)
  rw [ConstantCyclicSectionMap.component_toScheme,
    ConstantCyclicPullback.component_equivalence_assoc, ← Functor.map_comp,
    ConstantCyclicSectionMap.component_toScheme]
  change GroupSectionBaseChange.pullSection g P ^ i.val =
    GroupSectionBaseChange.pullSection g (P ^ i.val)
  exact (GroupSectionBaseChange.section_pow g P i.val).symm

/-- Every marked section in the original curve group commutes with arbitrary base change. -/
theorem generatorCurveMarking_pullback (i : Multiplicative (ZMod n)) :
    (H.baseChange g).generatorCurveMarking (hP.baseChange H g) i =
      GroupSectionBaseChange.pullSection g (H.generatorCurveMarking hP i) := by
  change (GroupSectionBaseChange.pullSection g P ^ i.toAdd.val) ≫
    (Over.pullback g).map H.inclusion =
      GroupSectionBaseChange.pullSection g ((P ^ i.toAdd.val) ≫ H.inclusion)
  rw [GroupSectionBaseChange.section_comp, GroupSectionBaseChange.section_pow]

variable [Etale H.carrier.hom]

/-- The canonical etale split isomorphism is preserved by arbitrary source change. -/
theorem etaleGeneratorSplitIso_pullback :
    let _ : Etale (H.baseChange g).carrier.hom :=
      inferInstanceAs (Etale (pullback.snd H.carrier.hom g))
    (H.baseChange g).etaleGeneratorSplitIso (hP.baseChange H g) =
      ConstantCyclicPullback.equivalence g n ≪≫
        (Over.pullback g).mapIso (H.etaleGeneratorSplitIso hP) := by
  dsimp only
  apply Iso.ext
  exact H.generatorCyclicMap_pullback hP g

end FLT.Mazur.GeneralizedEllipticCurve.FiniteSubgroup
