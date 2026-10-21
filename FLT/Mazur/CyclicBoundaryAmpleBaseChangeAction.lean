/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.CyclicBoundaryAmpleBaseChange
public import FLT.Mazur.CyclicBoundaryAmpleAction
public import FLT.Mazur.CyclicBoundaryFaithfulBaseChangeAction

/-!
# Equivariance of the actual ample boundary base-change projection

The common finite relabeling action commutes with the original faithful and
ample parameter projections. No quotient or geometric-point replacement is
needed to compare these actual scheme morphisms.
-/

@[expose] public noncomputable section
open CategoryTheory Limits AlgebraicGeometry
namespace FLT.Mazur.CyclicBoundaryParameter
open scoped CategoryTheory.Obj
open CyclicCharacteristicAtlas
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
section Faithful
variable {S T : Scheme} (g : T ⟶ S) (F : Over S) [GrpObj F] [IsSeparated F.hom]
  (n : ℕ) [NeZero n]

local instance faithfulActionProjectionPullback_separated :
    IsSeparated ((Over.pullback g).obj F).hom :=
  inferInstanceAs (IsSeparated (pullback.snd F.hom g))

/-- The original faithful projection commutes with every finite relabeling. -/
@[reassoc] theorem faithfulBaseChangeToOriginal_relabel (e : RelabelGroup n) :
    faithfulBaseChangeToOriginal g F n ≫ (faithfulRelabel F n e).left =
      (faithfulRelabel ((Over.pullback g).obj F) n e).left ≫
        faithfulBaseChangeToOriginal g F n := by
  have h := congrArg
    (fun f ↦ f.left ≫ pullback.fst (cyclicFaithfulParameter F n).hom g)
    (cyclicFaithfulBaseChange_inv_relabel g F n e)
  simpa only [Over.comp_left, Over.pullback_map_left, Category.assoc,
    pullback.lift_fst, faithfulBaseChangeToOriginal] using h

end Faithful

variable {S T : Scheme} (g : T ⟶ S) (E : GeneralizedEllipticCurve S)
  [IsSeparated E.group.hom] [SmoothOfRelativeDimension 1 E.group.hom]
  (n : ℕ) [NeZero n]

local instance ampleActionPullbackGroup_separated :
    IsSeparated (E.baseChange g).group.hom :=
  inferInstanceAs (IsSeparated (pullback.snd E.group.hom g))

local instance ampleActionPullbackGroup_smooth :
    SmoothOfRelativeDimension 1 (E.baseChange g).group.hom :=
  MorphismProperty.pullback_snd (P := @SmoothOfRelativeDimension 1) E.group.hom g
    inferInstance

local notation "q" => faithfulBaseChangeToOriginal g E.group n
local notation "a" => ampleBaseChangeToOriginal g E n

/-- The finite relabeling retains the actual ample parameter's structure morphism. -/
@[reassoc] theorem ampleRelabel_base (e : RelabelGroup n) :
    ampleRelabel E n e ≫ ampleParameterBase E n = ampleParameterBase E n := by
  change ampleRelabel E n e ≫ (ampleParameterOpen E n).ι ≫
    (cyclicFaithfulParameter E.group n).hom = _
  rw [ampleRelabel_inclusion_assoc]
  exact congrArg ((ampleParameterOpen E n).ι ≫ ·) (faithfulRelabel E.group n e).w

/-- The actual ample projection commutes with the original finite relabeling. -/
@[reassoc] theorem ampleBaseChangeToOriginal_relabel (e : RelabelGroup n) :
    (a) ≫ ampleRelabel E n e = ampleRelabel (E.baseChange g) n e ≫ (a) := by
  apply (cancel_mono (ampleParameterOpen E n).ι).mp
  rw [Category.assoc, ampleRelabel_inclusion, ampleBaseChangeToOriginal_inclusion_assoc,
    faithfulBaseChangeToOriginal_relabel]
  rw [Category.assoc, ampleBaseChangeToOriginal_inclusion, ampleRelabel_inclusion_assoc]
  rfl

/-- The comparison retains the given finite automorphism action on the actual ample schemes. -/
theorem ampleBaseChangeToOriginal_action (e : RelabelGroup n) :
    (a) ≫ (ampleAction E n e).hom = (ampleAction (E.baseChange g) n e).hom ≫ (a) :=
  ampleBaseChangeToOriginal_relabel g E n e

end FLT.Mazur.CyclicBoundaryParameter
