/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.OneGonAdicTripleSubgroupCoherence
public import FLT.Mazur.OneGonAdicExtendedCommonSubgroup

/-!
# Coherence of three actual pairwise pullbacks on their literal triple ring

Each pairwise comparison starts over its own literal supremum. After actual
pullback to the triple supremum and the proved compatible source identifications,
these three bundled subgroup comparisons satisfy the cocycle equation.
-/

@[expose] public noncomputable section
open CategoryTheory AlgebraicGeometry
namespace FLT.Mazur.OneGonAdicIndependentModel
open Approximation OneGonAdicCharacterTower OneGonSmoothing CharacterSchemeBaseChange
open ArithmeticOneGonGeneralizedCurve WeierstrassIntegralChart
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
variable {R : Type} [CommRing R] (I : Ideal R) [IsAdicComplete I R]
  (t : R) (ht : t ∈ I) (n : ℕ) [NeZero n] (s u v : Set R)
  (hs : complementaryInverse I t ht ∈ s) (hu : complementaryInverse I t ht ∈ u)

variable (i : (CoefficientStage (base I t ht n s))ᵒᵖ)
  (j : (CoefficientStage (base I t ht n u))ᵒᵖ)
  (b : (coefficientModelDiagram (base I t ht n s) (carrier I t ht n s).hom).obj i ⟶
    (integralSmoothOpen (equation (parameter I t ht n s))).toScheme)
  (hb : b ≫ (integralSmoothOpen (equation (parameter I t ht n s))).ι =
    (coefficientModelToInitial (base I t ht n s) (carrier I t ht n s).hom).app i ≫
      embedding I t ht n s)
  (c : (coefficientModelDiagram (base I t ht n u) (carrier I t ht n u).hom).obj j ⟶
    (integralSmoothOpen (equation (parameter I t ht n u))).toScheme)
  (hc : c ≫ (integralSmoothOpen (equation (parameter I t ht n u))).ι =
    (coefficientModelToInitial (base I t ht n u) (carrier I t ht n u).hom).app j ≫
      embedding I t ht n u)
  (hφs : Function.Surjective (OneGonFiniteCoefficientCoordinates.modelCoordinates t 1
    (canonicalCoordinates I t ht n) s))
  (hφu : Function.Surjective (OneGonFiniteCoefficientCoordinates.modelCoordinates t 1
    (canonicalCoordinates I t ht n) u))

variable (hv : complementaryInverse I t ht ∈ v)
  (k : (CoefficientStage (base I t ht n v))ᵒᵖ)
  (d : (coefficientModelDiagram (base I t ht n v) (carrier I t ht n v).hom).obj k ⟶
    (integralSmoothOpen (equation (parameter I t ht n v))).toScheme)
  (hd : d ≫ (integralSmoothOpen (equation (parameter I t ht n v))).ι =
    (coefficientModelToInitial (base I t ht n v) (carrier I t ht n v).hom).app k ≫
      embedding I t ht n v)
  (hφv : Function.Surjective (OneGonFiniteCoefficientCoordinates.modelCoordinates t 1
    (canonicalCoordinates I t ht n) v))

/-- The three actual pairwise pullback comparisons satisfy the full compatible cocycle. -/
theorem triplePairwiseFiniteSubgroupIso_trans :
    let L := tripleBase I t ht n s u v i j k
    (extendedCommonFiniteSubgroupIso I t ht n s u i j hs hu b hb c hc hφs hφu L
      (common_le_triple_first_second I t ht n s u v i j k)).trans
        (extendedCommonFiniteSubgroupIso I t ht n u v j k hu hv c hc d hd hφu hφv L
          (common_le_triple_second_third I t ht n s u v i j k)) =
    extendedCommonFiniteSubgroupIso I t ht n s v i k hs hv b hb d hd hφs hφv L
      (common_le_triple_first_third I t ht n s u v i j k) := by
  dsimp only
  rw [extendedCommonFiniteSubgroupIso_eq, extendedCommonFiniteSubgroupIso_eq,
    extendedCommonFiniteSubgroupIso_eq]
  apply sharedFiniteSubgroupIso_trans

end FLT.Mazur.OneGonAdicIndependentModel
