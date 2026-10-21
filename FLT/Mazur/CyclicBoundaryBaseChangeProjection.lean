/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.CyclicBoundaryFaithfulBaseChange

/-!
# The original-base projection of the faithful boundary comparison

The constructed map to the original faithful scheme is cartesian over the
actual base morphism. Every auxiliary and cyclic value has its exact original
group projection; these equations will identify the full universal subgroups.
-/

@[expose] public noncomputable section
open CategoryTheory Limits AlgebraicGeometry MonObj
open scoped CategoryTheory.Obj
namespace FLT.Mazur.CyclicBoundaryParameter
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
variable {S T : Scheme} (g : T ⟶ S) (E : Over S) [GrpObj E] [IsSeparated E.hom]
  (n : ℕ) [NeZero n]

local instance boundaryProjectionPullbackGroup_separated :
    IsSeparated ((Over.pullback g).obj E).hom :=
  inferInstanceAs (IsSeparated (pullback.snd E.hom g))

/-- The actual map from the new faithful boundary scheme to the original one. -/
def faithfulBaseChangeToOriginal :
    (cyclicFaithfulParameter ((Over.pullback g).obj E) n).left ⟶
      (cyclicFaithfulParameter E n).left :=
  (cyclicFaithfulBaseChangeIso g E n).inv.left ≫
    pullback.fst (cyclicFaithfulParameter E n).hom g

/-- The comparison preserves the original base map exactly. -/
@[reassoc] theorem faithfulBaseChangeToOriginal_base :
    faithfulBaseChangeToOriginal g E n ≫ (cyclicFaithfulParameter E n).hom =
      (cyclicFaithfulParameter ((Over.pullback g).obj E) n).hom ≫ g := by
  rw [faithfulBaseChangeToOriginal, Category.assoc, pullback.condition, ← Category.assoc]
  change ((cyclicFaithfulBaseChangeIso g E n).inv.left ≫
    ((Over.pullback g).obj (cyclicFaithfulParameter E n)).hom) ≫ g = _
  rw [Over.w]

/-- The actual faithful boundary comparison exhibits the original cartesian square. -/
theorem faithfulBaseChangeToOriginal_isPullback :
    IsPullback (faithfulBaseChangeToOriginal g E n)
      (cyclicFaithfulParameter ((Over.pullback g).obj E) n).hom
      (cyclicFaithfulParameter E n).hom g := by
  refine IsPullback.of_iso_pullback ⟨faithfulBaseChangeToOriginal_base g E n⟩
    ((Over.forget T).mapIso (cyclicFaithfulBaseChangeIso g E n).symm) rfl ?_
  exact (cyclicFaithfulBaseChangeIso g E n).inv.w

/-- All labels retain their actual original group-valued maps, including on nonfield tests. -/
@[reassoc] theorem faithfulBaseChangeToOriginal_value (a : Label n) :
    faithfulBaseChangeToOriginal g E n ≫ (cyclicFaithfulInclusion E n).left ≫
        (AuxiliaryLevel.value E (Label n) a).left =
      (cyclicFaithfulInclusion ((Over.pullback g).obj E) n).left ≫
        (AuxiliaryLevel.value ((Over.pullback g).obj E) (Label n) a).left ≫
          pullback.fst E.hom g := by
  have h : (cyclicFaithfulBaseChangeIso g E n).inv ≫
      (Over.pullback g).map (cyclicFaithfulInclusion E n ≫
        AuxiliaryLevel.value E (Label n) a) =
      cyclicFaithfulInclusion ((Over.pullback g).obj E) n ≫
        AuxiliaryLevel.value ((Over.pullback g).obj E) (Label n) a := by
    rw [Functor.map_comp, ← Category.assoc]
    change (cyclicFaithfulBaseChangeInv g E n ≫ _) ≫ _ = _
    rw [cyclicFaithfulBaseChangeInv_inclusion, Category.assoc]
    change _ ≫ AuxiliaryLevel.homSchemeBaseChangeInv g E (Label n) ≫ _ = _
    rw [AuxiliaryLevel.homSchemeBaseChangeInv_value]
  have hh := congrArg (fun f ↦ f.left ≫ pullback.fst E.hom g) h
  simpa only [Over.comp_left, Over.pullback_map_left, Category.assoc,
    pullback.lift_fst, faithfulBaseChangeToOriginal] using hh

end FLT.Mazur.CyclicBoundaryParameter
