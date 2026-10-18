/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.OddWeierstrassPointedCubicHomRetainedSubgroup
public import FLT.Mazur.OddWeierstrassAuxiliarySchemeMarking

/-!
# Original auxiliary sections on the pointed cubic cover

The independent auxiliary frame is taken from the actual cover of the original
pointed cubic. Projection through the source comparison recovers those sections.
-/

@[expose] public noncomputable section
open CategoryTheory Limits AlgebraicGeometry MonoidalCategory MonObj
namespace FLT.Mazur.OddWeierstrassParameter
open WeierstrassIntegralChart GeneralizedEllipticCurve AuxiliaryLevel
open UniversalWeierstrass (Labels)
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
variable {S : Scheme} (W : WeierstrassCurve Γ(S, ⊤)) [W.IsElliptic]
  (h₃ : IsUnit (3 : Γ(S, ⊤)))
local notation "k" => Over.hom (pointedCubicAuxiliaryCover W h₃)

/-- The original cubic group is separated over its base. -/
theorem pointedCubicOriginalAuxiliaryGroup_separated :
    IsSeparated (pointedCubicFamily W).group.hom :=
  inferInstanceAs (IsSeparated (pullback.snd (integralCurveStructure W) S.toSpecΓ))

attribute [local instance] pointedCubicOriginalAuxiliaryGroup_separated

/-- The auxiliary cover as a relative point over its own base map. -/
def pointedCubicAuxiliarySelfTest :
    (Over.map k).obj (𝟙_ (Over (pointedCubicAuxiliaryCover W h₃).left)) ⟶
      pointedCubicAuxiliaryCover W h₃ :=
  Over.homMk (𝟙 _) (by simp)

/-- The complete auxiliary marking on the actual pulled original cubic group. -/
def pointedCubicOriginalAuxiliaryMarking : Labels 3 →*
    (𝟙_ (Over (pointedCubicAuxiliaryCover W h₃).left) ⟶
      ((pointedCubicFamily W).baseChange k).group) :=
  GroupMarkingBaseChange.marking k (pointedCubicFamily W).group _
    (markingOf (pointedCubicFamily W).group (Labels 3)
      (pointedCubicAuxiliarySelfTest W h₃ ≫ pointedCubicAuxiliaryParameter W h₃ ≫
        faithfulInclusion _ _))

/-- The original auxiliary frame is faithful on every nonempty cover. -/
theorem pointedCubicOriginalAuxiliaryMarking_injective
    [Nonempty (pointedCubicAuxiliaryCover W h₃).left] :
    Function.Injective (pointedCubicOriginalAuxiliaryMarking W h₃) := by
  unfold pointedCubicOriginalAuxiliaryMarking
  apply (GroupMarkingBaseChange.marking_injective_iff _ _ _ _).mpr
  let _ : Nonempty ((Over.map k).obj
      (𝟙_ (Over (pointedCubicAuxiliaryCover W h₃).left))).left :=
    inferInstanceAs (Nonempty (pointedCubicAuxiliaryCover W h₃).left)
  exact faithful_marking_injective _ (Labels 3)
    (pointedCubicAuxiliarySelfTest W h₃ ≫ pointedCubicAuxiliaryParameter W h₃)

/-- Every original auxiliary label satisfies its prescribed power equation. -/
theorem pointedCubicOriginalAuxiliaryMarking_pow (i : Labels 3) :
    pointedCubicOriginalAuxiliaryMarking W h₃ i ^ 3 = 1 := by
  rw [← map_pow, UniversalWeierstrass.labels_pow, map_one]

/-- Projection recovers the independent auxiliary parameter on the original curve. -/
@[reassoc] theorem pointedCubicOriginalAuxiliaryMarking_fst (i : Labels 3) :
    (pointedCubicOriginalAuxiliaryMarking W h₃ i).left ≫
      pullback.fst (pointedCubicFamily W).group.hom k =
        (pointedCubicAuxiliaryParameter W h₃ ≫ faithfulInclusion _ _ ≫ value _ _ i).left := by
  refine (GroupMarkingBaseChange.marking_fst k (pointedCubicFamily W).group _
    (markingOf (pointedCubicFamily W).group (Labels 3)
      (pointedCubicAuxiliarySelfTest W h₃ ≫ pointedCubicAuxiliaryParameter W h₃ ≫
        faithfulInclusion _ _)) i).trans ?_
  change ((pointedCubicAuxiliarySelfTest W h₃ ≫ pointedCubicAuxiliaryParameter W h₃ ≫
    faithfulInclusion _ _) ≫ value _ _ i).left = _
  simp only [Over.comp_left, pointedCubicAuxiliarySelfTest,
    Over.homMk_left, Category.id_comp, Category.assoc]

variable {n : ℕ} [NeZero n]
  (φ : Multiplicative (ZMod n) →* (𝟙_ (Over S) ⟶ (pointedCubicFamily W).group))
local notation "f" => Over.Hom.left (pointedCubicHomAuxiliaryParameter W h₃ φ)

/-- The paired unrestricted parameter retains every original auxiliary coefficient value. -/
theorem pointedCubicHomAuxiliaryParameter_auxiliary (i : Labels 3) :
    cyclicHomAuxiliaryPoint n f ≫ (levelThreeMarking i).left =
      (pointedCubicAuxiliaryParameter W h₃ ≫ faithfulInclusion _ _ ≫ value _ _ i).left ≫
        (pointedCubicCoefficientGroupIso W h₃).hom.hom.hom.hom.left ≫
          pullback.fst universalGroup.hom (pointedCubicCoefficientBase W h₃) := by
  have ha := congrArg Over.Hom.left (cyclicHomLift_auxiliary n
    (pointedCubicFullCoefficientParameter W h₃ (Labels 3) (pointedCubicAuxiliaryParameter W h₃))
    (pointedCubicHomCoefficientParameter W h₃ φ))
  change cyclicHomAuxiliaryPoint n f = _ at ha
  rw [ha]
  exact pointedCubicFullCoefficientParameter_value W h₃ (Labels 3)
    (pointedCubicAuxiliaryParameter W h₃) i

/-- The full source comparison preserves the original independent auxiliary frame. -/
theorem pointedCubicHomSourceCurveIso_auxiliary (i : Labels 3) :
    pointedCubicOriginalAuxiliaryMarking W h₃ i ≫
      (pointedCubicHomSourceCurveIso W h₃ φ).hom.group =
        auxiliarySchemeMarking (cyclicHomAuxiliaryPoint n f) i := by
  apply auxiliarySchemeMarking_ext
  rw [Over.comp_left, Category.assoc]
  change (pointedCubicOriginalAuxiliaryMarking W h₃ i).left ≫
    (pointedCubicHomSourceGroupIso W h₃ φ).hom.hom.hom.hom.left ≫ _ = _
  rw [pointedCubicHomSourceGroupIso_fst, ← Category.assoc]
  change ((pointedCubicOriginalAuxiliaryMarking W h₃ i).left ≫
    pullback.fst (pointedCubicFamily W).group.hom k) ≫ _ = _
  rw [pointedCubicOriginalAuxiliaryMarking_fst]
  exact (pointedCubicHomAuxiliaryParameter_auxiliary W h₃ φ i).symm

end FLT.Mazur.OddWeierstrassParameter
