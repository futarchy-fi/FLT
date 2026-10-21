/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.OneGonAdicSharedCommonSubgroup
public import FLT.Mazur.OneGonAdicSharedSubgroupChangeRing

/-!
# Pullback of actual pairwise common subgroup comparisons

The original pairwise compatible comparison pulls back to the actual shared
comparison over any larger finite ring, including the literal triple supremum.
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
  (t : R) (ht : t ∈ I) (n : ℕ) [NeZero n] (s u : Set R)
  (i : (CoefficientStage (base I t ht n s))ᵒᵖ)
  (j : (CoefficientStage (base I t ht n u))ᵒᵖ)
  (hs : complementaryInverse I t ht ∈ s) (hu : complementaryInverse I t ht ∈ u)

variable
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

variable
  (hφs : Function.Surjective (OneGonFiniteCoefficientCoordinates.modelCoordinates t 1
    (canonicalCoordinates I t ht n) s))
  (hφu : Function.Surjective (OneGonFiniteCoefficientCoordinates.modelCoordinates t 1
    (canonicalCoordinates I t ht n) u))


variable (L : Subalgebra ℤ R) [Algebra.FiniteType ℤ L] (hKL : (commonBase I t ht n s u i j) ≤ L)

/-- Pullback from the literal pairwise ring agrees with the actual larger-ring comparison. -/
theorem commonFiniteSubgroupIso_changeRing :
    (sharedFiniteSubgroupTowerIso I t ht n s (commonBase I t ht n s u i j) L (base_le_common_left
        I t ht n s u i j) hKL
      i le_sup_left b hb hs hφs).trans
        ((commonFiniteSubgroupIso I t ht n s u i j hs hu b hb c hc hφs hφu).baseChange
          (sharedRingMap (commonBase I t ht n s u i j) L hKL)) =
    (sharedFiniteSubgroupIso I t ht n s u L (le_trans (base_le_common_left I t ht n s u i j) hKL)
        (le_trans (base_le_common_right I t ht n s u i j) hKL) hs hu
      i j (show stageBase I t ht n s i ≤ L from le_trans le_sup_left hKL)
        (show stageBase I t ht n u j ≤ L from le_trans le_sup_right hKL)
        b hb c hc hφs hφu).trans
        (sharedFiniteSubgroupTowerIso I t ht n u (commonBase I t ht n s u i j) L
            (base_le_common_right I t ht n s u i j) hKL
          j le_sup_right c hc hu hφu) := by
  simpa only [sharedFiniteSubgroupIso_common] using
    sharedFiniteSubgroupIso_changeRing I t ht n s u (commonBase I t ht n s u i j) L hKL
        (base_le_common_left I t ht n s u i j) (base_le_common_right I t ht n s u i j) hs hu i j
      le_sup_left le_sup_right b hb c hc hφs hφu

end FLT.Mazur.OneGonAdicIndependentModel
