/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.OneGonAdicIndependentFactorRecovery
public import FLT.Mazur.CharacterCoefficientHomDetection

/-!
# Group laws for arbitrary independent smooth stages

Injective coefficient recovery detects the group law on the full character
scheme and its product. The supplied factor is a homomorphism without any
flatness, reducedness, or invertibility assumption on its coefficient ring.
-/

@[expose] public noncomputable section
open CategoryTheory Limits AlgebraicGeometry
open scoped CategoryTheory.Obj
namespace FLT.Mazur.OneGonAdicIndependentModel
open Approximation OneGonAdicCharacterTower OneGonSmoothing CharacterSchemeBaseChange
open WeierstrassIntegralChart
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
variable {R : Type} [CommRing R] (I : Ideal R) [IsAdicComplete I R]
  (t : R) (ht : t ∈ I) (n : ℕ) [NeZero n] (s : Set R)
  (i : (CoefficientStage (base I t ht n s))ᵒᵖ)
  (b : (coefficientModelDiagram (base I t ht n s) (carrier I t ht n s).hom).obj i ⟶
    (integralSmoothOpen (equation (parameter I t ht n s))).toScheme)
  (hb : b ≫ (integralSmoothOpen (equation (parameter I t ht n s))).ι =
    (coefficientModelToInitial (base I t ht n s) (carrier I t ht n s).hom).app i ≫
      embedding I t ht n s)
  (hi : complementaryInverse I t ht ∈ s)

/-- The recovered intrinsic inclusion preserves the complete-base group law. -/
instance stageCharacterFactor_pullback_isMonHom :
    IsMonHom ((Over.pullback (baseMap (stageBase I t ht n s i) R)).map
      (stageCharacterFactor I t ht n s i b hb hi)) := by
  have he := stageCharacterFactor_recovery I t ht n s i b hb hi
  rw [← Iso.eq_inv_comp] at he
  rw [he]
  infer_instance

/-- The entire group law descends to the actual finite coefficient ring. -/
instance stageCharacterFactor_isMonHom :
    IsMonHom (stageCharacterFactor I t ht n s i b hb hi) := by
  let _ : IsSeparated (curve I t ht n s hi).group.hom :=
    inferInstanceAs (IsSeparated (integralSmoothStructure (equation (parameter I t ht n s))))
  let _ : IsSeparated (stageCurve I t ht n s i hi).group.hom :=
    MorphismProperty.pullback_snd _ _ inferInstance
  apply isMonHom_of_pullback (stageBase I t ht n s i) R (ZMod n)
    Subtype.val_injective (stageCurve I t ht n s i hi).group

end FLT.Mazur.OneGonAdicIndependentModel
