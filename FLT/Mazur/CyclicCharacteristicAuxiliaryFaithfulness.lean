/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.CyclicCharacteristicEvenParameterSource
public import FLT.Mazur.CyclicCharacteristicOddParameterSource
public import FLT.Mazur.CyclicCharacteristicNormalizedAuxiliary

/-!
# Universal faithfulness of the normalized auxiliary frames

Every nonempty test of either normalized chart has an injective auxiliary
frame. The proof compares with the actual source parameter, whose frame
comes from the faithful marking scheme, and keeps the full subgroup comparison.
-/

@[expose] public noncomputable section
open CategoryTheory AlgebraicGeometry MonoidalCategory
namespace FLT.Mazur.CyclicCharacteristicAtlas
open GeneralizedEllipticCurve GeneralizedEllipticCurve.FiniteSubgroup GroupSectionBaseChange
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
variable (n : ℕ) [NeZero n] {T : Scheme} [Nonempty T]

/-- Every nonempty test of the even normalized chart retains all sixteen labels. -/
theorem evenNormalizedAuxiliaryMarking_pull_injective (v : T ⟶ normalizedLocus n false) :
    Function.Injective (fun i ↦ pullSection v (evenNormalizedAuxiliaryMarking n i)) := by
  intro i j hij
  have h := congrArg (· ≫ (evenNormalizedParameterSourceIso n v).curve.hom.group) hij
  rw [evenNormalizedParameterSourceIso_auxiliary,
    evenNormalizedParameterSourceIso_auxiliary] at h
  exact UniversalWeierstrass.auxiliarySchemeMarking_injective _ h

/-- Every nonempty test of the odd normalized chart retains all nine labels. -/
theorem oddNormalizedAuxiliaryMarking_pull_injective (v : T ⟶ normalizedLocus n true) :
    Function.Injective (fun i ↦ pullSection v (oddNormalizedAuxiliaryMarking n i)) := by
  intro i j hij
  have h := congrArg (· ≫ (oddNormalizedParameterSourceIso n v).curve.hom.group) hij
  rw [oddNormalizedParameterSourceIso_auxiliary,
    oddNormalizedParameterSourceIso_auxiliary] at h
  exact OddWeierstrassParameter.auxiliarySchemeMarking_injective _ h

/-- Both normalized auxiliary frames are faithful after arbitrary nonempty base change. -/
theorem normalizedAuxiliaryMarking_pull_injective (b : Bool) (v : T ⟶ normalizedLocus n b) :
    Function.Injective (fun i ↦ pullSection v (normalizedAuxiliaryMarking n b i)) := by
  cases b
  · exact evenNormalizedAuxiliaryMarking_pull_injective n v
  · exact oddNormalizedAuxiliaryMarking_pull_injective n v

end FLT.Mazur.CyclicCharacteristicAtlas
