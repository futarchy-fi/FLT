/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.CyclicBoundaryAmpleBaseChange

/-!
# The ample boundary comparison retains the original modular family

The comparison of actual ample parameter schemes preserves their full universal
curves and finite subgroups. Consequently their modular transformations agree
on every scheme-valued test, including tests with nilpotents.
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

local instance ampleModuliPullbackGroup_separated :
    IsSeparated (E.baseChange g).group.hom :=
  inferInstanceAs (IsSeparated (pullback.snd E.group.hom g))

local instance ampleModuliPullbackGroup_smooth :
    SmoothOfRelativeDimension 1 (E.baseChange g).group.hom :=
  MorphismProperty.pullback_snd (P := @SmoothOfRelativeDimension 1) E.group.hom g
    inferInstance

local notation "a" => ampleBaseChangeToOriginal g E n

/-- The actual ample universal subgroups compare, retaining their full generalized curves. -/
def ampleBaseChangeSubgroupIso :
    CompatibleIso (ampleUniversalLevel (E.baseChange g) n).val.2
      ((ampleUniversalLevel E n).val.2.baseChange (a)) := by
  let c := faithfulBaseChangeTestSubgroupIso g E n (ampleParameterOpen (E.baseChange g) n).ι
  rw [← ampleBaseChangeToOriginal_inclusion g E n] at c
  exact c.trans ((faithfulUniversalSubgroup E n).compatibleBaseChangeComp
    (ampleParameterOpen E n).ι (a))

/-- The universal ample class is exactly the pullback of the original class. -/
theorem ampleUniversalClass_baseChange :
    ampleUniversalClass (E.baseChange g) n =
      ampleCyclicClassesPullback (a) n (ampleUniversalClass E n) :=
  Quotient.sound ⟨ampleBaseChangeSubgroupIso g E n⟩

/-- Every scheme test retains the original modular class under the comparison. -/
theorem ampleModuliMap_baseChange_apply {U : Scheme}
    (u : U ⟶ ampleParameter (E.baseChange g) n) :
    (ampleModuliMap (E.baseChange g) n).app (Opposite.op U) (ULift.up u) =
      (ampleModuliMap E n).app (Opposite.op U) (ULift.up (u ≫ (a))) := by
  change ampleCyclicClassesPullback u n (ampleUniversalClass (E.baseChange g) n) =
    ampleCyclicClassesPullback (u ≫ (a)) n (ampleUniversalClass E n)
  rw [ampleUniversalClass_baseChange g E n, ampleCyclicClassesPullback_comp]
  rfl

/-- The whole modular transformation commutes with the actual ample boundary projection. -/
theorem ampleModuliMap_baseChange :
    ampleModuliMap (E.baseChange g) n =
      uliftYoneda.map (a) ≫ ampleModuliMap E n := by
  ext U u
  exact ampleModuliMap_baseChange_apply g E n u.down

end FLT.Mazur.CyclicBoundaryParameter
