/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.CyclicBoundaryFaithfulAction
public import FLT.Mazur.CyclicBoundaryTestSubgroup
public import FLT.Mazur.RelativeCyclicSubgroupRelabel
public import FLT.Mazur.GeneralizedCurveBaseChangeCompEq

/-!
# Relabeling the actual universal boundary subgroup

The lifted finite action preserves the full pulled-back curve and its subgroup.
The comparison uses the original cyclic labels and the actual base-change maps.
-/

@[expose] public noncomputable section
open CategoryTheory Limits AlgebraicGeometry MonoidalCategory MonObj
namespace FLT.Mazur.CyclicBoundaryParameter
open GeneralizedEllipticCurve CyclicCharacteristicAtlas
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
variable {S : Scheme} (E : GeneralizedEllipticCurve S) (n : ℕ) [NeZero n]
  [IsSeparated E.group.hom] (e : RelabelGroup n)
local notation "P" => cyclicFaithfulParameter E.group n
local notation "a" => Over.Hom.left (faithfulRelabel E.group n e)
local notation "φ" => faithfulUniversalMarking E n
local notation "H" => faithfulUniversalSubgroup E n

/-- The full universal boundary curve is preserved by the lifted relabeling. -/
def faithfulRelabelCurveIso : faithfulUniversalCurve E n ≅
    (faithfulUniversalCurve E n).baseChange (a) :=
  E.baseChangeCompEqIso (P).hom (a) (P).hom (faithfulRelabel E.group n e).w.symm

/-- The curve comparison preserves the original group projection. -/
@[reassoc] theorem faithfulRelabelCurveIso_fst :
    (faithfulRelabelCurveIso E n e).hom.group.left ≫
      pullback.fst (faithfulUniversalCurve E n).group.hom (a) ≫
        pullback.fst E.group.hom (P).hom = pullback.fst E.group.hom (P).hom :=
  E.baseChangeCompEqIso_group_fst (P).hom (a) (P).hom _

/-- The curve comparison retains precisely the relabeled original cyclic section. -/
theorem faithfulRelabelCurveIso_section (i : Multiplicative (ZMod n)) :
    (φ) (e.2.2.symm i) ≫ (faithfulRelabelCurveIso E n e).hom.group =
      GroupSectionBaseChange.pullSection (a) ((φ) i) := by
  apply OverPullbackSection.hom_ext
  apply pullback.hom_ext
  · simp only [Over.comp_left, Category.assoc, faithfulRelabelCurveIso_fst,
      GroupSectionBaseChange.section_fst_assoc]
    change (cyclicSectionMarking E.group n (P).hom
      (cyclicFaithfulInclusion E.group n) (e.2.2.symm i)).left ≫ _ = _
    rw [cyclicSectionMarking_apply, section_fst]
    change _ = (a) ≫ (cyclicSectionMarking E.group n (P).hom
      (cyclicFaithfulInclusion E.group n) i).left ≫ _
    rw [cyclicSectionMarking_apply, section_fst]
    have h := congrArg Over.Hom.left
      (congrArg (fun f ↦ f ≫ AuxiliaryLevel.value E.group (Label n) (1, 1, i))
        (faithfulRelabel_inclusion E.group n e))
    simpa only [Category.assoc, action_cyclic, Over.comp_left] using h.symm
  · have hp (s : 𝟙_ (Over (P).left) ⟶
        (Over.pullback (a)).obj (faithfulUniversalCurve E n).group) :
        (s.left ≫ pullback.fst (faithfulUniversalCurve E n).group.hom (a)) ≫
          (faithfulUniversalCurve E n).group.hom = (a) := by
        rw [Category.assoc, pullback.condition, ← Category.assoc]
        change (s.left ≫ ((Over.pullback (a)).obj
          (faithfulUniversalCurve E n).group).hom) ≫ (a) = (a)
        rw [s.w]
        exact Category.id_comp _
    exact (hp _).trans (hp _).symm

/-- Pullback along relabeling is the subgroup built from the permuted cyclic marking. -/
def faithfulRelabelSubgroupPullbackIso :
    FiniteSubgroup.CompatibleIso
      ((faithfulUniversalCurve E n).relativeCyclicSubgroup
        ((φ).comp e.2.2.symm.toMonoidHom)
        (relativeCyclicMarking_relabel_distinct _ (φ)
          (faithfulUniversalMarking_distinct E n) e.2.2.symm))
      ((H).baseChange (a)) :=
  relativeCyclicSubgroupPullbackCompatibleIso (a) (φ) _
    (faithfulUniversalMarking_distinct E n) _ (faithfulRelabelCurveIso E n e)
    (faithfulRelabelCurveIso_section E n e)

/-- The actual universal subgroup is preserved, including its full-curve inclusion. -/
def faithfulRelabelSubgroupIso : FiniteSubgroup.CompatibleIso ((H).baseChange (a)) (H) :=
  (faithfulRelabelSubgroupPullbackIso E n e).symm.trans
    (relativeCyclicSubgroupRelabelIso (faithfulUniversalCurve E n) (φ)
      (faithfulUniversalMarking_distinct E n) e.2.2.symm)

/-- Relabeling preserves ampleness of the universal subgroup. -/
theorem faithfulRelabelSubgroup_isAmple_iff : ((H).baseChange (a)).IsAmple ↔ (H).IsAmple :=
  (faithfulRelabelSubgroupIso E n e).isAmple_iff

end FLT.Mazur.CyclicBoundaryParameter
