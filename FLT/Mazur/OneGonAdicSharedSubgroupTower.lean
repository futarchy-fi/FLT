/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.OneGonAdicSharedEmbeddingTower

/-!
# Compatible subgroup comparisons under extension of the shared ring

The refined supplied subgroup over the larger ring is compatibly isomorphic
to the actual pullback from the smaller shared ring. The comparison uses the
full curve tower map and the intrinsic character coefficient isomorphism.
-/

@[expose] public noncomputable section
open CategoryTheory AlgebraicGeometry
open scoped CategoryTheory.Obj
namespace FLT.Mazur.OneGonAdicIndependentModel
open Approximation OneGonAdicCharacterTower OneGonSmoothing CharacterSchemeBaseChange
open ArithmeticOneGonGeneralizedCurve WeierstrassIntegralChart
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
variable {R : Type} [CommRing R] (I : Ideal R) [IsAdicComplete I R]
  (t : R) (ht : t ∈ I) (n : ℕ) [NeZero n] (s : Set R)
  (K L : Subalgebra ℤ R) [Algebra.FiniteType ℤ K] [Algebra.FiniteType ℤ L]
  (hS : base I t ht n s ≤ K) (hKL : K ≤ L)

variable (i : (CoefficientStage (base I t ht n s))ᵒᵖ)
  (hi : stageBase I t ht n s i ≤ K)
  (b : (coefficientModelDiagram (base I t ht n s) (carrier I t ht n s).hom).obj i ⟶
    (integralSmoothOpen (equation (parameter I t ht n s))).toScheme)
  (hb : b ≫ (integralSmoothOpen (equation (parameter I t ht n s))).ι =
    (coefficientModelToInitial (base I t ht n s) (carrier I t ht n s).hom).app i ≫
      embedding I t ht n s)
  (hs : complementaryInverse I t ht ∈ s)
  (hφ : Function.Surjective (OneGonFiniteCoefficientCoordinates.modelCoordinates t 1
    (canonicalCoordinates I t ht n) s))

/-- Shared-ring extension preserves the whole actual finite subgroup with its source group. -/
def sharedFiniteSubgroupTowerIso : GeneralizedEllipticCurve.FiniteSubgroup.CompatibleIso
    (S := Spec (.of L))
    (sharedFiniteSubgroup I t ht n s L (hS.trans hKL) i (hi.trans hKL) b hb hs hφ)
    ((sharedFiniteSubgroup I t ht n s K hS i hi b hb hs hφ).baseChange
      (sharedRingMap K L hKL)) where
  curve := sharedCurveTowerIso I t ht n s K L hS hKL hs
  subgroup := @overIso K L (ZMod n) _ _ (sharedRingAlgebra K L hKL) _
  isMonHom := by
    let _ := sharedRingAlgebra K L hKL
    exact inferInstanceAs (IsMonHom (overIso K L (ZMod n)).hom)
  compatible := by
    rw [GeneralizedEllipticCurve.FiniteSubgroup.baseChange_curveMap]
    rw [sharedFiniteSubgroup_curveMap, sharedFiniteSubgroup_curveMap]
    exact shared_intrinsic_embedding_tower I t ht n s K L hS hKL hs

end FLT.Mazur.OneGonAdicIndependentModel
