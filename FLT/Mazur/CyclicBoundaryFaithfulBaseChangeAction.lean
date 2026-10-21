/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.CyclicBoundaryFaithfulBaseChange
public import FLT.Mazur.CyclicBoundaryFaithfulAction

/-!
# The faithful boundary base-change comparison is equivariant

The common finite relabeling action commutes with the constructed isomorphism
of faithful boundary schemes, with its original inverse convention unchanged.
-/

@[expose] public noncomputable section
open CategoryTheory Limits AlgebraicGeometry MonObj
open scoped CategoryTheory.Obj
namespace FLT.Mazur.CyclicBoundaryParameter
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
variable {S T : Scheme} (g : T ⟶ S) (E : Over S) [GrpObj E] [IsSeparated E.hom]
  (n : ℕ) [NeZero n]

local instance boundaryActionPullbackGroup_separated :
    IsSeparated ((Over.pullback g).obj E).hom :=
  inferInstanceAs (IsSeparated (pullback.snd E.hom g))

/-- The entire faithful parameter comparison commutes with each original relabeling. -/
@[reassoc] theorem cyclicFaithfulBaseChange_relabel (e : CyclicCharacteristicAtlas.RelabelGroup n) :
    (cyclicFaithfulBaseChangeIso g E n).hom ≫ faithfulRelabel ((Over.pullback g).obj E) n e =
      (Over.pullback g).map (faithfulRelabel E n e) ≫
        (cyclicFaithfulBaseChangeIso g E n).hom := by
  apply (cancel_mono (cyclicFaithfulInclusion ((Over.pullback g).obj E) n)).mp
  change (cyclicFaithfulBaseChangeHom g E n ≫ faithfulRelabel _ n e) ≫ _ =
    ((Over.pullback g).map (faithfulRelabel E n e) ≫ cyclicFaithfulBaseChangeHom g E n) ≫ _
  rw [Category.assoc, faithfulRelabel_inclusion,
    cyclicFaithfulBaseChangeHom_inclusion_assoc, parameterBaseChange_action,
    Category.assoc, cyclicFaithfulBaseChangeHom_inclusion,
    ← Category.assoc ((Over.pullback g).map (faithfulRelabel E n e)),
    ← Functor.map_comp, faithfulRelabel_inclusion, Functor.map_comp, Category.assoc]

/-- The actual inverse comparison is equivariant too. -/
@[reassoc] theorem cyclicFaithfulBaseChange_inv_relabel
    (e : CyclicCharacteristicAtlas.RelabelGroup n) :
    (cyclicFaithfulBaseChangeIso g E n).inv ≫ (Over.pullback g).map (faithfulRelabel E n e) =
      faithfulRelabel ((Over.pullback g).obj E) n e ≫
        (cyclicFaithfulBaseChangeIso g E n).inv := by
  apply (cancel_mono (cyclicFaithfulBaseChangeIso g E n).hom).mp
  rw [Category.assoc, ← cyclicFaithfulBaseChange_relabel, Iso.inv_hom_id_assoc,
    Category.assoc, Iso.inv_hom_id, Category.comp_id]

end FLT.Mazur.CyclicBoundaryParameter
