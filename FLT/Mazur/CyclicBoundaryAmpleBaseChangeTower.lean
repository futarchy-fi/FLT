/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.CyclicBoundaryAmpleBaseChange

/-!
# Tower comparison for the actual ample boundary schemes

The composite of the two original parameter projections is cartesian. Its
universal property constructs a canonical isomorphism from iterated to direct
base change, retaining both the original ample parameter and the final base.
-/

@[expose] public noncomputable section
open CategoryTheory Limits AlgebraicGeometry
namespace FLT.Mazur.CyclicBoundaryParameter
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
variable {S T U : Scheme} (g : T ⟶ S) (h : U ⟶ T) (E : GeneralizedEllipticCurve S)
  [IsSeparated E.group.hom] [SmoothOfRelativeDimension 1 E.group.hom]
  (n : ℕ) [NeZero n]

local instance ampleTowerPullbackGroup_separated {V W : Scheme}
    (F : GeneralizedEllipticCurve V) [IsSeparated F.group.hom] (f : W ⟶ V) :
    IsSeparated (F.baseChange f).group.hom :=
  inferInstanceAs (IsSeparated (pullback.snd F.group.hom f))

local instance ampleTowerPullbackGroup_smooth {V W : Scheme}
    (F : GeneralizedEllipticCurve V) [SmoothOfRelativeDimension 1 F.group.hom] (f : W ⟶ V) :
    SmoothOfRelativeDimension 1 (F.baseChange f).group.hom :=
  MorphismProperty.pullback_snd (P := @SmoothOfRelativeDimension 1) F.group.hom f
    inferInstance

/-- The iterated ample parameter retains its original cartesian projection over the composite. -/
theorem ampleBaseChangeTower_isPullback :
    IsPullback (ampleBaseChangeToOriginal h (E.baseChange g) n ≫
        ampleBaseChangeToOriginal g E n)
      (ampleParameterBase ((E.baseChange g).baseChange h) n)
      (ampleParameterBase E n) (h ≫ g) :=
  (ampleBaseChangeToOriginal_isPullback h (E.baseChange g) n).paste_horiz
    (ampleBaseChangeToOriginal_isPullback g E n)

/-- The canonical comparison between the actual iterated and direct ample boundary schemes. -/
def ampleBaseChangeTowerIso :
    ampleParameter ((E.baseChange g).baseChange h) n ≅
      ampleParameter (E.baseChange (h ≫ g)) n :=
  (ampleBaseChangeTower_isPullback g h E n).isoIsPullback _ _
    (ampleBaseChangeToOriginal_isPullback (h ≫ g) E n)

/-- The tower comparison retains the composite of the original ample projections. -/
@[reassoc] theorem ampleBaseChangeTowerIso_original :
    (ampleBaseChangeTowerIso g h E n).hom ≫ ampleBaseChangeToOriginal (h ≫ g) E n =
      ampleBaseChangeToOriginal h (E.baseChange g) n ≫ ampleBaseChangeToOriginal g E n :=
  (ampleBaseChangeTower_isPullback g h E n).isoIsPullback_hom_fst _ _
    (ampleBaseChangeToOriginal_isPullback (h ≫ g) E n)

/-- The tower comparison retains the actual final structure morphism. -/
@[reassoc] theorem ampleBaseChangeTowerIso_base :
    (ampleBaseChangeTowerIso g h E n).hom ≫ ampleParameterBase (E.baseChange (h ≫ g)) n =
      ampleParameterBase ((E.baseChange g).baseChange h) n :=
  (ampleBaseChangeTower_isPullback g h E n).isoIsPullback_hom_snd _ _
    (ampleBaseChangeToOriginal_isPullback (h ≫ g) E n)

/-- The two original projections uniquely characterize the actual tower comparison. -/
theorem ampleBaseChangeTowerIso_hom_unique
    (f : ampleParameter ((E.baseChange g).baseChange h) n ⟶
      ampleParameter (E.baseChange (h ≫ g)) n)
    (hf : f ≫ ampleBaseChangeToOriginal (h ≫ g) E n =
      ampleBaseChangeToOriginal h (E.baseChange g) n ≫ ampleBaseChangeToOriginal g E n)
    (hb : f ≫ ampleParameterBase (E.baseChange (h ≫ g)) n =
      ampleParameterBase ((E.baseChange g).baseChange h) n) :
    f = (ampleBaseChangeTowerIso g h E n).hom :=
  (ampleBaseChangeToOriginal_isPullback (h ≫ g) E n).hom_ext
    (hf.trans (ampleBaseChangeTowerIso_original g h E n).symm)
    (hb.trans (ampleBaseChangeTowerIso_base g h E n).symm)

/-- Base change along the identity gives an isomorphism to the original ample scheme. -/
instance ampleBaseChangeToOriginal_id_isIso : IsIso (ampleBaseChangeToOriginal (𝟙 S) E n) :=
  (ampleBaseChangeToOriginal_isPullback (𝟙 S) E n).isIso_fst_of_isIso

/-- The actual identity comparison of ample boundary schemes. -/
def ampleBaseChangeIdIso : ampleParameter (E.baseChange (𝟙 S)) n ≅ ampleParameter E n :=
  asIso (ampleBaseChangeToOriginal (𝟙 S) E n)

end FLT.Mazur.CyclicBoundaryParameter
