/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.CyclicBoundaryAmpleBaseChangeTower
public import FLT.Mazur.CyclicBoundaryAmpleBaseChangeRefinement

/-!
# Three-stage coherence of actual ample parameter towers

Both parenthesizations of the three-stage comparison agree as scheme maps.
The first-stage comparison is lifted through the last cartesian square; neither
route is defined by the equality to be proved.
-/

@[expose] public noncomputable section
open CategoryTheory Limits AlgebraicGeometry
namespace FLT.Mazur.CyclicBoundaryParameter
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
variable {S T U V : Scheme} (g : T ⟶ S) (h : U ⟶ T) (k : V ⟶ U)
  (E : GeneralizedEllipticCurve S)
  [IsSeparated E.group.hom] [SmoothOfRelativeDimension 1 E.group.hom]
  (n : ℕ) [NeZero n]

local instance ampleTripleGroup_separated {X Y : Scheme}
    (F : GeneralizedEllipticCurve X) [IsSeparated F.group.hom] (f : Y ⟶ X) :
    IsSeparated (F.baseChange f).group.hom :=
  inferInstanceAs (IsSeparated (pullback.snd F.group.hom f))

local instance ampleTripleGroup_smooth {X Y : Scheme}
    (F : GeneralizedEllipticCurve X) [SmoothOfRelativeDimension 1 F.group.hom] (f : Y ⟶ X) :
    SmoothOfRelativeDimension 1 (F.baseChange f).group.hom :=
  MorphismProperty.pullback_snd (P := @SmoothOfRelativeDimension 1) F.group.hom f
    inferInstance

local notation "D" => GeneralizedEllipticCurve.baseChange
  (GeneralizedEllipticCurve.baseChange (GeneralizedEllipticCurve.baseChange E g) h) k

/-- The full three-stage parameter projection is cartesian over the composite base map. -/
theorem ampleTripleTower_isPullback :
    IsPullback (ampleBaseChangeToOriginal k ((E.baseChange g).baseChange h) n ≫
        ampleBaseChangeToOriginal h (E.baseChange g) n ≫ ampleBaseChangeToOriginal g E n)
      (ampleParameterBase (D) n) (ampleParameterBase E n) (k ≫ (h ≫ g)) :=
  (ampleBaseChangeToOriginal_isPullback k ((E.baseChange g).baseChange h) n).paste_horiz
    (ampleBaseChangeTower_isPullback g h E n)

/-- The direct three-stage comparison retains the final base and the original parameter. -/
def ampleTripleTowerIso : ampleParameter (D) n ≅ ampleParameter (E.baseChange (k ≫ (h ≫ g))) n :=
  (ampleTripleTower_isPullback g h k E n).isoIsPullback _ _
    (ampleBaseChangeToOriginal_isPullback (k ≫ (h ≫ g)) E n)

/-- Lift the first two stages' existing tower comparison through the final cartesian square. -/
def ampleTowerFirstLift :
    ampleParameter (D) n ⟶ ampleParameter ((E.baseChange (h ≫ g)).baseChange k) n :=
  (ampleBaseChangeToOriginal_isPullback k (E.baseChange (h ≫ g)) n).lift
    (ampleBaseChangeToOriginal k ((E.baseChange g).baseChange h) n ≫
      (ampleBaseChangeTowerIso g h E n).hom) (ampleParameterBase (D) n) (by
        rw [Category.assoc, ampleBaseChangeTowerIso_base]
        exact (ampleBaseChangeToOriginal_isPullback k ((E.baseChange g).baseChange h) n).w)

/-- The lifted comparison retains the original two-stage comparison. -/
@[reassoc] theorem ampleTowerFirstLift_original :
    ampleTowerFirstLift g h k E n ≫
        ampleBaseChangeToOriginal k (E.baseChange (h ≫ g)) n =
      ampleBaseChangeToOriginal k ((E.baseChange g).baseChange h) n ≫
        (ampleBaseChangeTowerIso g h E n).hom :=
  (ampleBaseChangeToOriginal_isPullback k (E.baseChange (h ≫ g)) n).lift_fst _ _ _

/-- The first-stage lift preserves the actual final structure map. -/
@[reassoc] theorem ampleTowerFirstLift_base :
    ampleTowerFirstLift g h k E n ≫
      ampleParameterBase ((E.baseChange (h ≫ g)).baseChange k) n = ampleParameterBase (D) n :=
  (ampleBaseChangeToOriginal_isPullback k (E.baseChange (h ≫ g)) n).lift_snd _ _ _

/-- Comparing the first two stages and then the last agrees with the direct triple comparison. -/
theorem ampleTripleTower_first :
    ampleTowerFirstLift g h k E n ≫ (ampleBaseChangeTowerIso (h ≫ g) k E n).hom =
      (ampleTripleTowerIso g h k E n).hom := by
  apply (ampleBaseChangeToOriginal_isPullback (k ≫ (h ≫ g)) E n).hom_ext
  · rw [Category.assoc, ampleBaseChangeTowerIso_original, ampleTowerFirstLift_original_assoc,
      ampleBaseChangeTowerIso_original]
    exact ((ampleTripleTower_isPullback g h k E n).isoIsPullback_hom_fst _ _
      (ampleBaseChangeToOriginal_isPullback (k ≫ (h ≫ g)) E n)).symm
  · rw [Category.assoc, ampleBaseChangeTowerIso_base, ampleTowerFirstLift_base]
    exact ((ampleTripleTower_isPullback g h k E n).isoIsPullback_hom_snd _ _
      (ampleBaseChangeToOriginal_isPullback (k ≫ (h ≫ g)) E n)).symm

/-- Comparing the last two stages and then the first gives the same actual triple comparison. -/
theorem ampleTripleTower_last :
    (ampleBaseChangeTowerIso h k (E.baseChange g) n).hom ≫
      (ampleBaseChangeTowerIso g (k ≫ h) E n).hom ≫
        ampleBaseRefinement E n (k ≫ (h ≫ g)) ((k ≫ h) ≫ g) (𝟙 V)
          (by rw [Category.id_comp, Category.assoc]) =
      (ampleTripleTowerIso g h k E n).hom := by
  apply (ampleBaseChangeToOriginal_isPullback (k ≫ (h ≫ g)) E n).hom_ext
  · simp only [Category.assoc, ampleBaseRefinement_original,
      ampleBaseChangeTowerIso_original, ampleBaseChangeTowerIso_original_assoc]
    exact ((ampleTripleTower_isPullback g h k E n).isoIsPullback_hom_fst _ _
      (ampleBaseChangeToOriginal_isPullback (k ≫ (h ≫ g)) E n)).symm
  · simp only [Category.assoc, ampleBaseRefinement_base, Category.comp_id,
      ampleBaseChangeTowerIso_base]
    exact ((ampleTripleTower_isPullback g h k E n).isoIsPullback_hom_snd _ _
      (ampleBaseChangeToOriginal_isPullback (k ≫ (h ≫ g)) E n)).symm

end FLT.Mazur.CyclicBoundaryParameter
