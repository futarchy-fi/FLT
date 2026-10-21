/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.CyclicBoundaryBaseChangeSubgroup
public import FLT.Mazur.CyclicBoundaryAmpleModuli
public import FLT.Mazur.CompatibleSubgroupIsoBaseChange

/-!
# Ampleness under the actual boundary base-change comparison

The full universal subgroup comparison preserves and reflects ampleness on
arbitrary scheme tests. It identifies the ample open without reducedness or
smoothness assumptions on the base morphism.
-/

@[expose] public noncomputable section
open CategoryTheory Limits AlgebraicGeometry
namespace FLT.Mazur.CyclicBoundaryParameter
open GeneralizedEllipticCurve.FiniteSubgroup
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
variable {S T : Scheme} (g : T ⟶ S) (E : GeneralizedEllipticCurve S)
  [IsSeparated E.group.hom] [SmoothOfRelativeDimension 1 E.group.hom]
  (n : ℕ) [NeZero n]

local instance boundaryAmplePullbackGroup_separated :
    IsSeparated (E.baseChange g).group.hom :=
  inferInstanceAs (IsSeparated (pullback.snd E.group.hom g))

local instance boundaryAmplePullbackGroup_smooth :
    SmoothOfRelativeDimension 1 (E.baseChange g).group.hom :=
  MorphismProperty.pullback_snd (P := @SmoothOfRelativeDimension 1) E.group.hom g
    inferInstance

local notation "Q" =>
  cyclicFaithfulParameter (GeneralizedEllipticCurve.group (E.baseChange g)) n
local notation "q" => faithfulBaseChangeToOriginal g E.group n
local notation "H" => faithfulUniversalSubgroup E n
local notation "J" => faithfulUniversalSubgroup (E.baseChange g) n

/-- Every new-base test retains the actual original universal subgroup and whole curve. -/
def faithfulBaseChangeTestSubgroupIso {U : Scheme} (u : U ⟶ (Q).left) :
    CompatibleIso ((J).baseChange u) ((H).baseChange (u ≫ (q))) :=
  ((faithfulBaseChangeSubgroupIso g E n).baseChange u).trans
    ((H).compatibleBaseChangeComp (q) u).symm

omit [SmoothOfRelativeDimension 1 E.group.hom] in
/-- Ampleness is preserved and reflected on all tests of the faithful comparison. -/
theorem faithfulBaseChangeTest_isAmple_iff {U : Scheme} (u : U ⟶ (Q).left) :
    ((J).baseChange u).IsAmple ↔ ((H).baseChange (u ≫ (q))).IsAmple :=
  (faithfulBaseChangeTestSubgroupIso g E n u).isAmple_iff

/-- A test lies in the new ample open exactly when its original parameter does. -/
theorem ampleParameter_baseChange_criterion {U : Scheme} (u : U ⟶ (Q).left) :
    Set.range u ⊆ ampleParameterOpen (E.baseChange g) n ↔
      Set.range (u ≫ (q)) ⊆ ampleParameterOpen E n :=
  ((J).isAmple_baseChange_iff_range
    (faithfulUniversalSubgroup_cartier (E.baseChange g) n).1 u).symm.trans
      ((faithfulBaseChangeTest_isAmple_iff g E n u).trans
        ((H).isAmple_baseChange_iff_range (faithfulUniversalSubgroup_cartier E n).1 _))

/-- The actual ample boundary comparison to the original parameter. -/
def ampleBaseChangeToOriginal : ampleParameter (E.baseChange g) n ⟶ ampleParameter E n :=
  (H).ampleOpenLift (faithfulUniversalSubgroup_cartier E n).1
    ((ampleParameterOpen (E.baseChange g) n).ι ≫ (q))
    ((faithfulBaseChangeTest_isAmple_iff g E n _).mp
      ((J).ampleOpen_isAmple (faithfulUniversalSubgroup_cartier (E.baseChange g) n).1))

/-- The ample comparison retains the actual faithful parameter projection. -/
@[reassoc] theorem ampleBaseChangeToOriginal_inclusion :
    ampleBaseChangeToOriginal g E n ≫ (ampleParameterOpen E n).ι =
      (ampleParameterOpen (E.baseChange g) n).ι ≫ (q) :=
  (H).ampleOpenLift_inclusion _ _ _

end FLT.Mazur.CyclicBoundaryParameter
