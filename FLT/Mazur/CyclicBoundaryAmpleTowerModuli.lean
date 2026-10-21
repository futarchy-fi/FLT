/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.CyclicBoundaryAmpleBaseChangeTower
public import FLT.Mazur.CyclicBoundaryAmpleBaseChangeModuli

/-!
# The ample boundary tower comparison preserves the modular family

Both iterated and direct base change preserve the original modular class on
every test. The actual tower isomorphism therefore commutes with the full
modular transformation, rather than only its geometric points.
-/

@[expose] public noncomputable section
open CategoryTheory Limits AlgebraicGeometry
namespace FLT.Mazur.CyclicBoundaryParameter
open GeneralizedEllipticCurve.FiniteSubgroup
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
variable {S T U : Scheme} (g : T ⟶ S) (h : U ⟶ T) (E : GeneralizedEllipticCurve S)
  [IsSeparated E.group.hom] [SmoothOfRelativeDimension 1 E.group.hom]
  (n : ℕ) [NeZero n]

local instance ampleTowerModuliPullbackGroup_separated {V W : Scheme}
    (F : GeneralizedEllipticCurve V) [IsSeparated F.group.hom] (f : W ⟶ V) :
    IsSeparated (F.baseChange f).group.hom :=
  inferInstanceAs (IsSeparated (pullback.snd F.group.hom f))

local instance ampleTowerModuliPullbackGroup_smooth {V W : Scheme}
    (F : GeneralizedEllipticCurve V) [SmoothOfRelativeDimension 1 F.group.hom] (f : W ⟶ V) :
    SmoothOfRelativeDimension 1 (F.baseChange f).group.hom :=
  MorphismProperty.pullback_snd (P := @SmoothOfRelativeDimension 1) F.group.hom f
    inferInstance

/-- Iterated base change compares the actual universal subgroup with the original one. -/
def ampleBaseChangeTowerSubgroupIso :
    CompatibleIso (ampleUniversalLevel ((E.baseChange g).baseChange h) n).val.2
      ((ampleUniversalLevel E n).val.2.baseChange
        (ampleBaseChangeToOriginal h (E.baseChange g) n ≫
          ampleBaseChangeToOriginal g E n)) :=
  (ampleBaseChangeSubgroupIso h (E.baseChange g) n).trans
    (((ampleBaseChangeSubgroupIso g E n).baseChange
      (ampleBaseChangeToOriginal h (E.baseChange g) n)).trans
        ((ampleUniversalLevel E n).val.2.compatibleBaseChangeComp
          (ampleBaseChangeToOriginal g E n)
          (ampleBaseChangeToOriginal h (E.baseChange g) n)).symm)

/-- The actual tower isomorphism retains the full curve and actual finite subgroup. -/
def ampleTowerIsoSubgroupIso :
    CompatibleIso (ampleUniversalLevel ((E.baseChange g).baseChange h) n).val.2
      ((ampleUniversalLevel (E.baseChange (h ≫ g)) n).val.2.baseChange
        (ampleBaseChangeTowerIso g h E n).hom) := by
  let c := ((ampleBaseChangeSubgroupIso (h ≫ g) E n).baseChange
    (ampleBaseChangeTowerIso g h E n).hom).trans
      ((ampleUniversalLevel E n).val.2.compatibleBaseChangeComp
        (ampleBaseChangeToOriginal (h ≫ g) E n) (ampleBaseChangeTowerIso g h E n).hom).symm
  rw [ampleBaseChangeTowerIso_original] at c
  exact (ampleBaseChangeTowerSubgroupIso g h E n).trans c.symm

/-- Iterated ample base change retains the full original universal modular class. -/
theorem ampleUniversalClass_baseChange_tower :
    ampleUniversalClass ((E.baseChange g).baseChange h) n =
      ampleCyclicClassesPullback (ampleBaseChangeToOriginal h (E.baseChange g) n ≫
        ampleBaseChangeToOriginal g E n) n (ampleUniversalClass E n) := by
  rw [ampleUniversalClass_baseChange h (E.baseChange g) n,
    ampleUniversalClass_baseChange g E n, ampleCyclicClassesPullback_comp]
  rfl

/-- The actual tower isomorphism identifies the direct and iterated universal classes. -/
theorem ampleUniversalClass_towerIso :
    ampleUniversalClass ((E.baseChange g).baseChange h) n =
      ampleCyclicClassesPullback (ampleBaseChangeTowerIso g h E n).hom n
        (ampleUniversalClass (E.baseChange (h ≫ g)) n) :=
  Quotient.sound ⟨ampleTowerIsoSubgroupIso g h E n⟩

/-- The original modular transformations commute with the actual tower isomorphism. -/
theorem ampleModuliMap_towerIso :
    ampleModuliMap ((E.baseChange g).baseChange h) n =
      uliftYoneda.map (ampleBaseChangeTowerIso g h E n).hom ≫
        ampleModuliMap (E.baseChange (h ≫ g)) n := by
  ext V v
  change ampleCyclicClassesPullback v.down n
      (ampleUniversalClass ((E.baseChange g).baseChange h) n) =
    ampleCyclicClassesPullback (v.down ≫ (ampleBaseChangeTowerIso g h E n).hom) n
      (ampleUniversalClass (E.baseChange (h ≫ g)) n)
  rw [ampleUniversalClass_towerIso g h E n, ampleCyclicClassesPullback_comp]
  rfl

end FLT.Mazur.CyclicBoundaryParameter
