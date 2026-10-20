/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.CyclicBoundaryFaithfulLift
public import FLT.Mazur.CyclicBoundaryTestSubgroup
public import FLT.Mazur.GeneralizedCurveBaseChangeCompEq

/-!
# The faithful lift retains the original test subgroup

The comparison uses the entire original generalized curve over the given base
map. It identifies the reconstructed subgroup with universal base change.
-/

@[expose] public noncomputable section
open CategoryTheory Limits AlgebraicGeometry MonoidalCategory MonObj
namespace FLT.Mazur.CyclicBoundaryParameter
open GeneralizedEllipticCurve
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
variable {S : Scheme} (E : GeneralizedEllipticCurve S) (n : ℕ) [NeZero n]
  [IsSeparated E.group.hom] {T : Scheme} (g : T ⟶ S)
  (f : Over.mk g ⟶ parameter E.group n)
  (hf : UniversallyDistinctSections.UniversallyDistinct
    (fun i : ZMod n ↦ cyclicSectionMarking E.group n g f (.ofAdd i)))
local notation "P" => cyclicFaithfulParameter E.group n
local notation "u" => cyclicFaithfulLift E.group n g f hf

/-- The faithful lift preserves the full original test curve. -/
def cyclicFaithfulLiftCurveIso : E.baseChange g ≅
    (faithfulUniversalCurve E n).baseChange (u).left :=
  E.baseChangeCompEqIso (P).hom (u).left g (u).w.symm

/-- The lifted comparison preserves the original group projection. -/
@[reassoc] theorem cyclicFaithfulLiftCurveIso_fst :
    (cyclicFaithfulLiftCurveIso E n g f hf).hom.group.left ≫
      pullback.fst (faithfulUniversalCurve E n).group.hom (u).left ≫
        pullback.fst E.group.hom (P).hom = pullback.fst E.group.hom g :=
  E.baseChangeCompEqIso_group_fst (P).hom (u).left g _

/-- The lifted curve comparison retains every original cyclic section. -/
theorem cyclicFaithfulLiftCurveIso_section (i : Multiplicative (ZMod n)) :
    cyclicSectionMarking E.group n g f i ≫ (cyclicFaithfulLiftCurveIso E n g f hf).hom.group =
      GroupSectionBaseChange.pullSection (u).left (faithfulUniversalMarking E n i) := by
  apply OverPullbackSection.hom_ext
  apply pullback.hom_ext
  · simp only [Over.comp_left, Category.assoc, cyclicFaithfulLiftCurveIso_fst,
      GroupSectionBaseChange.section_fst_assoc]
    rw [cyclicSectionMarking_apply, section_fst]
    change _ = (u).left ≫ (cyclicSectionMarking E.group n (P).hom
      (cyclicFaithfulInclusion E.group n) i).left ≫ _
    rw [cyclicSectionMarking_apply, section_fst]
    have h := congrArg Over.Hom.left (cyclicFaithfulLift_inclusion E.group n g f hf)
    simpa only [Over.comp_left, Category.assoc] using
      congrArg (fun k ↦ k ≫ (AuxiliaryLevel.value E.group (Label n) (1, 1, i)).left) h.symm
  · have hp (s : 𝟙_ (Over T) ⟶
        (Over.pullback (u).left).obj (faithfulUniversalCurve E n).group) :
        (s.left ≫ pullback.fst (faithfulUniversalCurve E n).group.hom (u).left) ≫
          (faithfulUniversalCurve E n).group.hom = (u).left := by
        rw [Category.assoc, pullback.condition, ← Category.assoc]
        change (s.left ≫ ((Over.pullback (u).left).obj
          (faithfulUniversalCurve E n).group).hom) ≫ (u).left = (u).left
        rw [s.w]
        exact Category.id_comp _
    exact (hp _).trans (hp _).symm

/-- The original test subgroup is the actual universal subgroup pulled back along its lift. -/
def cyclicFaithfulLiftSubgroupIso :
    FiniteSubgroup.CompatibleIso
      ((E.baseChange g).relativeCyclicSubgroup (cyclicSectionMarking E.group n g f) hf)
      ((faithfulUniversalSubgroup E n).baseChange (u).left) :=
  relativeCyclicSubgroupPullbackCompatibleIso
    (E := faithfulUniversalCurve E n) (F := E.baseChange g) (u).left
    (faithfulUniversalMarking E n)
    (cyclicSectionMarking E.group n g f) (faithfulUniversalMarking_distinct E n) hf
    (cyclicFaithfulLiftCurveIso E n g f hf) (cyclicFaithfulLiftCurveIso_section E n g f hf)

end FLT.Mazur.CyclicBoundaryParameter
