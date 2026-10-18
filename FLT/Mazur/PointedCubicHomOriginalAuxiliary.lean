/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.PointedCubicHomRetainedSubgroup
public import FLT.Mazur.UniversalWeierstrassAuxiliarySchemeMarking

/-!
# Original auxiliary sections on the pointed cubic cover

The independent auxiliary frame is taken from the actual cover of the original
pointed cubic. Projection through the source comparison recovers those sections.
-/

@[expose] public noncomputable section
open CategoryTheory Limits AlgebraicGeometry MonoidalCategory MonObj
namespace FLT.Mazur.GeneralizedEllipticCurve
open WeierstrassIntegralChart UniversalWeierstrass AuxiliaryLevel
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
variable {S : Scheme} (W : WeierstrassCurve Γ(S, ⊤)) [W.IsElliptic]
  (h₂ : IsUnit (2 : Γ(S, ⊤)))
local notation "k" => Over.hom (pointedCubicAuxiliaryCover W h₂)

/-- The original cubic group is separated over its base. -/
theorem pointedCubicOriginalAuxiliaryGroup_separated :
    IsSeparated (pointedCubicFamily W).group.hom :=
  inferInstanceAs (IsSeparated (pullback.snd (integralCurveStructure W) S.toSpecΓ))

attribute [local instance] pointedCubicOriginalAuxiliaryGroup_separated

/-- The auxiliary cover as a relative point over its own base map. -/
def pointedCubicAuxiliarySelfTest :
    (Over.map k).obj (𝟙_ (Over (pointedCubicAuxiliaryCover W h₂).left)) ⟶
      pointedCubicAuxiliaryCover W h₂ :=
  Over.homMk (𝟙 _) (by simp)

/-- The complete auxiliary marking on the actual pulled original cubic group. -/
def pointedCubicOriginalAuxiliaryMarking : Labels 4 →*
    (𝟙_ (Over (pointedCubicAuxiliaryCover W h₂).left) ⟶
      ((pointedCubicFamily W).baseChange k).group) :=
  GroupMarkingBaseChange.marking k (pointedCubicFamily W).group _
    (markingOf (pointedCubicFamily W).group (Labels 4)
      (pointedCubicAuxiliarySelfTest W h₂ ≫ pointedCubicAuxiliaryParameter W h₂ ≫
        faithfulInclusion _ _))

/-- The original auxiliary frame is faithful on every nonempty cover. -/
theorem pointedCubicOriginalAuxiliaryMarking_injective
    [Nonempty (pointedCubicAuxiliaryCover W h₂).left] :
    Function.Injective (pointedCubicOriginalAuxiliaryMarking W h₂) := by
  unfold pointedCubicOriginalAuxiliaryMarking
  apply (GroupMarkingBaseChange.marking_injective_iff _ _ _ _).mpr
  let _ : Nonempty ((Over.map k).obj
      (𝟙_ (Over (pointedCubicAuxiliaryCover W h₂).left))).left :=
    inferInstanceAs (Nonempty (pointedCubicAuxiliaryCover W h₂).left)
  exact faithful_marking_injective _ (Labels 4)
    (pointedCubicAuxiliarySelfTest W h₂ ≫ pointedCubicAuxiliaryParameter W h₂)

/-- Every original auxiliary label satisfies its prescribed power equation. -/
theorem pointedCubicOriginalAuxiliaryMarking_pow (i : Labels 4) :
    pointedCubicOriginalAuxiliaryMarking W h₂ i ^ 4 = 1 := by
  rw [← map_pow, labels_pow, map_one]

/-- Projection recovers the independent auxiliary parameter on the original curve. -/
@[reassoc] theorem pointedCubicOriginalAuxiliaryMarking_fst (i : Labels 4) :
    (pointedCubicOriginalAuxiliaryMarking W h₂ i).left ≫
      pullback.fst (pointedCubicFamily W).group.hom k =
        (pointedCubicAuxiliaryParameter W h₂ ≫ faithfulInclusion _ _ ≫ value _ _ i).left := by
  refine (GroupMarkingBaseChange.marking_fst k (pointedCubicFamily W).group _
    (markingOf (pointedCubicFamily W).group (Labels 4)
      (pointedCubicAuxiliarySelfTest W h₂ ≫ pointedCubicAuxiliaryParameter W h₂ ≫
        faithfulInclusion _ _)) i).trans ?_
  change ((pointedCubicAuxiliarySelfTest W h₂ ≫ pointedCubicAuxiliaryParameter W h₂ ≫
    faithfulInclusion _ _) ≫ value _ _ i).left = _
  simp only [Over.comp_left, pointedCubicAuxiliarySelfTest,
    Over.homMk_left, Category.id_comp, Category.assoc]

variable {n : ℕ} [NeZero n]
  (φ : Multiplicative (ZMod n) →* (𝟙_ (Over S) ⟶ (pointedCubicFamily W).group))
local notation "f" => Over.Hom.left (pointedCubicHomAuxiliaryParameter W h₂ φ)

/-- The paired unrestricted parameter retains every original auxiliary coefficient value. -/
theorem pointedCubicHomAuxiliaryParameter_auxiliary (i : Labels 4) :
    cyclicHomAuxiliaryPoint n f ≫ (auxiliaryMarking 4 i).left =
      (pointedCubicAuxiliaryParameter W h₂ ≫ faithfulInclusion _ _ ≫ value _ _ i).left ≫
        (pointedCubicCoefficientGroupIso W h₂).hom.hom.hom.hom.left ≫
          pullback.fst universalGroup.hom (pointedCubicCoefficientBase W h₂) := by
  have ha := congrArg Over.Hom.left (cyclicHomLift_auxiliary n
    (pointedCubicFullCoefficientParameter W h₂ (Labels 4) (pointedCubicAuxiliaryParameter W h₂))
    (pointedCubicHomCoefficientParameter W h₂ φ))
  change cyclicHomAuxiliaryPoint n f = _ at ha
  rw [ha]
  exact pointedCubicFullCoefficientParameter_value W h₂ (Labels 4)
    (pointedCubicAuxiliaryParameter W h₂) i

/-- The full source comparison preserves the original independent auxiliary frame. -/
theorem pointedCubicHomSourceCurveIso_auxiliary (i : Labels 4) :
    pointedCubicOriginalAuxiliaryMarking W h₂ i ≫
      (pointedCubicHomSourceCurveIso W h₂ φ).hom.group =
        auxiliarySchemeMarking (cyclicHomAuxiliaryPoint n f) i := by
  apply auxiliarySchemeMarking_ext
  rw [Over.comp_left, Category.assoc]
  change (pointedCubicOriginalAuxiliaryMarking W h₂ i).left ≫
    (pointedCubicHomSourceGroupIso W h₂ φ).hom.hom.hom.hom.left ≫ _ = _
  rw [pointedCubicHomSourceGroupIso_fst, ← Category.assoc]
  change ((pointedCubicOriginalAuxiliaryMarking W h₂ i).left ≫
    pullback.fst (pointedCubicFamily W).group.hom k) ≫ _ = _
  rw [pointedCubicOriginalAuxiliaryMarking_fst]
  exact (pointedCubicHomAuxiliaryParameter_auxiliary W h₂ φ i).symm

end FLT.Mazur.GeneralizedEllipticCurve
