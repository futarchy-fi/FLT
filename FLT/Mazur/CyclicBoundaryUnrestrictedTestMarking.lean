/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.CyclicBoundaryUnrestrictedOrbit
public import FLT.Mazur.GeneralizedCurveBaseChangeCompEq
public import FLT.Mazur.CyclicMarkingDivisorTransport

/-!
# Original boundary tests retain their full unrestricted universal markings

The comparison uses the original base map of a test and keeps every auxiliary
and cyclic label. No faithful-marking hypothesis is imposed.
-/

@[expose] public noncomputable section
open CategoryTheory Limits AlgebraicGeometry MonoidalCategory MonObj
namespace FLT.Mazur.CyclicBoundaryParameter
open GeneralizedEllipticCurve
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
variable {S T : Scheme} (E : GeneralizedEllipticCurve S) (n : ℕ) [NeZero n]
  (g : T ⟶ S) (f : Over.mk g ⟶ parameter E.group n)
local notation "B" => parameter E.group n

/-- The comparison preserves the full original test curve over its given base map. -/
def unrestrictedTestCurveIso :
    E.baseChange g ≅ (unrestrictedUniversalCurve E n).baseChange f.left :=
  E.baseChangeCompEqIso (B).hom f.left g f.w.symm

/-- The full comparison retains the original group projection. -/
@[reassoc] theorem unrestrictedTestCurveIso_fst :
    (unrestrictedTestCurveIso E n g f).hom.group.left ≫
      pullback.fst (unrestrictedUniversalCurve E n).group.hom f.left ≫
        pullback.fst E.group.hom (B).hom = pullback.fst E.group.hom g :=
  E.baseChangeCompEqIso_group_fst (B).hom f.left g _

/-- Every original label is the universal label pulled back along the actual test. -/
theorem unrestrictedTestCurveIso_label (j : Label n) :
    markedSection E.group n g f j ≫ (unrestrictedTestCurveIso E n g f).hom.group =
      GroupSectionBaseChange.pullSection f.left (markedSection E.group n (B).hom (𝟙 (B)) j) := by
  apply OverPullbackSection.hom_ext
  apply pullback.hom_ext
  · have hs := GroupSectionBaseChange.section_fst f.left
      (show 𝟙_ (Over (B).left) ⟶ (unrestrictedUniversalCurve E n).group from
        markedSection E.group n (B).hom (𝟙 (B)) j)
    simp only [Over.comp_left, Category.assoc, unrestrictedTestCurveIso_fst]
    rw [← Category.assoc, hs, Category.assoc, section_fst, section_fst]
    change f.left ≫ (AuxiliaryLevel.value E.group (Label n) j).left =
      f.left ≫ 𝟙 (B).left ≫ (AuxiliaryLevel.value E.group (Label n) j).left
    exact (congrArg (fun k ↦ f.left ≫ k) (Category.id_comp _)).symm
  · have hp (s : 𝟙_ (Over T) ⟶
        (Over.pullback f.left).obj (unrestrictedUniversalCurve E n).group) :
        (s.left ≫ pullback.fst (unrestrictedUniversalCurve E n).group.hom f.left) ≫
          (unrestrictedUniversalCurve E n).group.hom = f.left := by
        rw [Category.assoc, pullback.condition, ← Category.assoc]
        change (s.left ≫ ((Over.pullback f.left).obj
          (unrestrictedUniversalCurve E n).group).hom) ≫ f.left = f.left
        rw [s.w]
        exact Category.id_comp _
    exact (hp _).trans (hp _).symm

/-- The actual cyclic section comparison is the cyclic factor of the full label comparison. -/
theorem unrestrictedTestCurveIso_section (i : Multiplicative (ZMod n)) :
    cyclicSectionMarking E.group n g f i ≫ (unrestrictedTestCurveIso E n g f).hom.group =
      pullCyclicMarking f.left (unrestrictedUniversalMarking E n) i := by
  change cyclicSectionMarking E.group n g f i ≫ _ =
    GroupSectionBaseChange.pullSection f.left (unrestrictedUniversalMarking E n i)
  have hm : unrestrictedUniversalMarking E n i =
      markedSection E.group n (B).hom (𝟙 (B)) (1, 1, i) :=
    cyclicSectionMarking_apply E.group n (B).hom (𝟙 (B)) i
  rw [cyclicSectionMarking_apply, hm]
  exact unrestrictedTestCurveIso_label E n g f (1, 1, i)

/-- The full ideal retains all occurrences of each original cyclic label. -/
theorem unrestrictedTestCurveIso_ideal :
    ((unrestrictedUniversalCurve E n).baseChange f.left).cyclicMarkingIdeal
        (pullCyclicMarking f.left (unrestrictedUniversalMarking E n)) =
      ((E.baseChange g).cyclicMarkingIdeal (cyclicSectionMarking E.group n g f)).comap
        (unrestrictedTestCurveIso E n g f).inv.curve.left :=
  cyclicMarkingIdeal_transport _ _ (unrestrictedTestCurveIso E n g f)
    (unrestrictedTestCurveIso_section E n g f)

end FLT.Mazur.CyclicBoundaryParameter
