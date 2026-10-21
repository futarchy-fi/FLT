/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.OneGonAdicIndependentFiniteSubgroup
public import FLT.Mazur.CompatibleSubgroupIsoBaseChange

/-!
# Compatible recovery of arbitrary independent finite subgroups

The full generalized curve and its rank-n subgroup recover together. Both
isomorphisms are the constructed coefficient comparisons, and the subgroup
square follows from the proved intrinsic whole-embedding recovery.
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

variable (hφ : Function.Surjective (OneGonFiniteCoefficientCoordinates.modelCoordinates t 1
  (canonicalCoordinates I t ht n) s))

/-- Recover the actual complete-base finite subgroup as compatible full geometric data. -/
def stageFiniteSubgroupRecoveryIso : GeneralizedEllipticCurve.FiniteSubgroup.CompatibleIso
    (canonicalFiniteSubgroup I t ht n)
    ((stageFiniteSubgroup I t ht n s i b hb hi hφ).baseChange
      (baseMap (stageBase I t ht n s i) R)) where
  curve := stageGeneralizedRecoveryIso I t ht n s i hi
  subgroup := overIso (stageBase I t ht n s i) R (ZMod n)
  isMonHom := inferInstanceAs
    (IsMonHom (overIso (stageBase I t ht n s i) R (ZMod n)).hom)
  compatible := by
    rw [GeneralizedEllipticCurve.FiniteSubgroup.baseChange_curveMap,
      stageFiniteSubgroup_curveMap]
    exact (stage_intrinsic_embedding_recovery I t ht n s i hi).symm

/-- The compatible recovery retains the actual full generalized-curve comparison. -/
theorem stageFiniteSubgroupRecoveryIso_curve :
    (stageFiniteSubgroupRecoveryIso I t ht n s i b hb hi hφ).curve =
      stageGeneralizedRecoveryIso I t ht n s i hi := rfl

/-- The compatible recovery retains the intrinsic character coefficient comparison. -/
theorem stageFiniteSubgroupRecoveryIso_subgroup :
    (stageFiniteSubgroupRecoveryIso I t ht n s i b hb hi hφ).subgroup =
      overIso (stageBase I t ht n s i) R (ZMod n) := rfl

end FLT.Mazur.OneGonAdicIndependentModel
