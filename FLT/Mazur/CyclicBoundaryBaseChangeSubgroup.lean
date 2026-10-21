/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.CyclicBoundaryBaseChangeCurve
public import FLT.Mazur.RelativeCyclicSubgroupPullbackComparison

/-!
# The actual universal boundary subgroup commutes with base change

Every cyclic label is the pullback of its original section under the full
curve comparison. This constructs a compatible isomorphism of the actual finite
subgroups and retains the original generator, including over singular bases.
-/

@[expose] public noncomputable section
open CategoryTheory Limits AlgebraicGeometry MonoidalCategory MonObj
namespace FLT.Mazur.CyclicBoundaryParameter
open GeneralizedEllipticCurve
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
variable {S T : Scheme} (g : T ⟶ S) (E : GeneralizedEllipticCurve S)
  [IsSeparated E.group.hom] (n : ℕ) [NeZero n]

local instance boundarySubgroupPullbackGroup_separated :
    IsSeparated (E.baseChange g).group.hom :=
  inferInstanceAs (IsSeparated (pullback.snd E.group.hom g))

local notation "P" => cyclicFaithfulParameter E.group n
local notation "Q" =>
  cyclicFaithfulParameter (GeneralizedEllipticCurve.group (E.baseChange g)) n
local notation "q" => faithfulBaseChangeToOriginal g E.group n
local notation "F" => faithfulUniversalCurve E n
local notation "G" => faithfulUniversalCurve (E.baseChange g) n
local notation "φ" => faithfulUniversalMarking E n
local notation "ψ" => faithfulUniversalMarking (E.baseChange g) n

/-- Each universal cyclic marking retains its original group-valued parameter. -/
@[reassoc] theorem faithfulUniversalMarking_original_fst (i : Multiplicative (ZMod n)) :
    ((φ) i).left ≫ pullback.fst E.group.hom (P).hom =
      (cyclicFaithfulInclusion E.group n).left ≫
        (AuxiliaryLevel.value E.group (Label n) (1, 1, i)).left := by
  have h := congrArg (fun s ↦ s.left ≫ pullback.fst E.group.hom (P).hom)
    (cyclicSectionMarking_apply E.group n (P).hom (cyclicFaithfulInclusion E.group n) i)
  exact h.trans (section_fst E.group n (P).hom (cyclicFaithfulInclusion E.group n) (1, 1, i))

/-- Every actual cyclic label is preserved by the full universal-curve comparison. -/
theorem faithfulBaseChangeCurveIso_section (i : Multiplicative (ZMod n)) :
    (ψ) i ≫ (faithfulBaseChangeCurveIso g E n).hom.group =
      GroupSectionBaseChange.pullSection (q) ((φ) i) := by
  apply OverPullbackSection.hom_ext
  apply pullback.hom_ext
  · simp only [Over.comp_left, Category.assoc, faithfulBaseChangeCurveIso_group_fst,
      GroupSectionBaseChange.section_fst_assoc]
    change ((ψ) i).left ≫ pullback.fst (E.baseChange g).group.hom (Q).hom ≫
        pullback.fst E.group.hom g =
      (q) ≫ ((φ) i).left ≫ pullback.fst E.group.hom (P).hom
    have hn := congrArg (· ≫ pullback.fst E.group.hom g)
      (faithfulUniversalMarking_original_fst (E.baseChange g) n i)
    have ho := congrArg ((q) ≫ ·) (faithfulUniversalMarking_original_fst E n i).symm
    simp only [Category.assoc] at hn
    exact hn.trans
      ((faithfulBaseChangeToOriginal_value g E.group n (1, 1, i)).symm.trans ho)
  · have hp (s : 𝟙_ (Over (Q).left) ⟶ ((F).baseChange (q)).group) :
        (s.left ≫ pullback.fst (F).group.hom (q)) ≫ (F).group.hom = (q) := by
      rw [Category.assoc, pullback.condition, ← Category.assoc]
      change (s.left ≫ ((F).baseChange (q)).group.hom) ≫ (q) = (q)
      rw [s.w]
      exact Category.id_comp _
    exact (hp _).trans (hp _).symm

/-- The actual finite boundary subgroups compare under arbitrary base change. -/
def faithfulBaseChangeSubgroupIso :
    FiniteSubgroup.CompatibleIso (faithfulUniversalSubgroup (E.baseChange g) n)
      ((faithfulUniversalSubgroup E n).baseChange (q)) :=
  relativeCyclicSubgroupPullbackCompatibleIso (q) (φ) (ψ)
    (faithfulUniversalMarking_distinct E n) (faithfulUniversalMarking_distinct (E.baseChange g) n)
    (faithfulBaseChangeCurveIso g E n) (faithfulBaseChangeCurveIso_section g E n)

/-- The compatible subgroup isomorphism retains the actual whole-curve comparison. -/
theorem faithfulBaseChangeSubgroupIso_curve :
    (faithfulBaseChangeSubgroupIso g E n).curve = faithfulBaseChangeCurveIso g E n := rfl

/-- The component-one generator is retained under the actual monoidal pullback. -/
theorem faithfulBaseChangeSubgroupIso_generator :
    (G).relativeCyclicGenerator (ψ) (faithfulUniversalMarking_distinct (E.baseChange g) n) ≫
        (faithfulBaseChangeSubgroupIso g E n).subgroup.hom =
      GroupSectionBaseChange.pullSection (q)
        ((F).relativeCyclicGenerator (φ) (faithfulUniversalMarking_distinct E n)) :=
  relativeCyclicSubgroupPullbackCompatibleIso_generator (q) (φ) (ψ)
    (faithfulUniversalMarking_distinct E n) (faithfulUniversalMarking_distinct (E.baseChange g) n)
    (faithfulBaseChangeCurveIso g E n) (faithfulBaseChangeCurveIso_section g E n)

end FLT.Mazur.CyclicBoundaryParameter
