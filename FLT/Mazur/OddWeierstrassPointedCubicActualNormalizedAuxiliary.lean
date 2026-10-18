/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.OddWeierstrassPointedCubicHomOriginalAuxiliary
public import FLT.Mazur.OddWeierstrassPointedCubicActualNormalizedGenerator
public import FLT.Mazur.CyclicCharacteristicOddNormalizedAuxiliary

/-!
# The actual normalized atlas retains the original cubic auxiliary frame

Compose normalization, equality of orbit ideals, and the original cubic
comparison. The resulting full comparison retains the independent auxiliary
frame on the original family as well as its already specified Cartier generator.
-/

@[expose] public noncomputable section
open CategoryTheory AlgebraicGeometry MonoidalCategory
namespace FLT.Mazur.OddWeierstrassParameter
open GeneralizedEllipticCurve CyclicCharacteristicAtlas
open GeneralizedEllipticCurve.FiniteSubgroup GroupSectionBaseChange
open UniversalWeierstrass (Labels)
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
variable {S : Scheme} (W : WeierstrassCurve Γ(S, ⊤)) [W.IsElliptic]
  (h₃ : IsUnit (3 : Γ(S, ⊤))) {n : ℕ} [NeZero n]
  (H : (pointedCubicFamily W).FiniteSubgroup n)
  {P : 𝟙_ (Over S) ⟶ H.carrier} (hP : H.IsCartierGenerator P)
local notation "φ" => H.generatorCurveMarking hP
local notation "k" => Over.hom (pointedCubicAuxiliaryCover W h₃)
local notation "f" => Over.Hom.left (pointedCubicHomAuxiliaryParameter W h₃ φ)
local notation "hf" => pointedCubicHomPrescribed_equation W h₃ H hP
local notation "fN" => cyclicHomNormalizedPoint n f
local notation "q" => cyclicHomNormalizedLocusPoint n f hf
local notation "J" => pointedCubicHomRetainedSubgroup W h₃ φ H
local notation "hJ" => pointedCubicHomRetained_ideal W h₃ φ H hP rfl

/-- The normalized source retains the original auxiliary frame on the actual cubic cover. -/
theorem pointedCubicHomNormalizedOriginalIso_auxiliary (i : Labels 3) :
    auxiliarySchemeMarking (cyclicHomAuxiliaryPoint n fN) i ≫
      (pointedCubicHomNormalizedOriginalIso W h₃ H hP).curve.hom.group =
        pointedCubicOriginalAuxiliaryMarking W h₃ i := by
  apply CompatibleIso.group_section_trans
    (cyclicHomNormalizedPrescribedSubgroupIso n f hf J hJ)
    (pointedCubicHomRetainedIso W h₃ φ H).symm _
    (auxiliarySchemeMarking (cyclicHomAuxiliaryPoint n f) i) _
  · change _ ≫ ((cyclicHomNormalizationSubgroupIso n f hf).curve.hom.group ≫ 𝟙 _) = _
    rw [Category.comp_id]
    exact cyclicHomNormalizationSubgroupIso_auxiliary n f hf i
  · exact CompatibleIso.group_section_symm (pointedCubicHomRetainedIso W h₃ φ H) _ _
      (pointedCubicHomSourceCurveIso_auxiliary W h₃ φ i)

/-- The actual chart-to-original comparison preserves every independent auxiliary label. -/
theorem pointedCubicActualNormalizedIso_auxiliary (i : Labels 3) :
    pullSection q (oddNormalizedAuxiliaryMarking n i) ≫
      (pointedCubicActualNormalizedIso W h₃ H hP).curve.hom.group =
        pointedCubicOriginalAuxiliaryMarking W h₃ i := by
  exact CompatibleIso.group_section_trans (oddNormalizedSourceIso n f hf)
    (pointedCubicHomNormalizedOriginalIso W h₃ H hP) _ _ _
    (oddNormalizedSourceIso_auxiliary n f hf i)
    (pointedCubicHomNormalizedOriginalIso_auxiliary W h₃ H hP i)

end FLT.Mazur.OddWeierstrassParameter
