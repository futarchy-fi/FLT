/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.OneGonAdicCommonSubgroupChangeRing

/-!
# Pairwise subgroup comparisons transported to a larger finite ring

Conjugating the actual pullback comparison by the proved subgroup tower maps
recovers the intrinsic comparison of the two supplied stages in the larger ring.
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

/-- Pull back the original pairwise comparison and identify its two actual source subgroups. -/
def extendedCommonFiniteSubgroupIso :=
  ((sharedFiniteSubgroupTowerIso I t ht n s (commonBase I t ht n s u i j) L (base_le_common_left I
      t ht n s u i j) hKL
    i le_sup_left b hb hs hφs).trans
      ((commonFiniteSubgroupIso I t ht n s u i j hs hu b hb c hc hφs hφu).baseChange
        (sharedRingMap (commonBase I t ht n s u i j) L hKL))).trans
          (sharedFiniteSubgroupTowerIso I t ht n u (commonBase I t ht n s u i j) L
              (base_le_common_right I t ht n s u i j) hKL
            j le_sup_right c hc hu hφu).symm

/-- The transported whole pairwise comparison is the constructed larger-ring comparison. -/
theorem extendedCommonFiniteSubgroupIso_eq :
    extendedCommonFiniteSubgroupIso I t ht n s u i j hs hu b hb c hc hφs hφu L hKL =
      sharedFiniteSubgroupIso I t ht n s u L (le_trans (base_le_common_left I t ht n s u i j) hKL)
          (le_trans (base_le_common_right I t ht n s u i j) hKL) hs hu
        i j (le_sup_left.trans hKL) (le_sup_right.trans hKL) b hb c hc hφs hφu := by
  unfold extendedCommonFiniteSubgroupIso
  rw [commonFiniteSubgroupIso_changeRing,
    GeneralizedEllipticCurve.FiniteSubgroup.CompatibleIso.trans_assoc,
    GeneralizedEllipticCurve.FiniteSubgroup.CompatibleIso.trans_symm,
    GeneralizedEllipticCurve.FiniteSubgroup.CompatibleIso.trans_refl]

end FLT.Mazur.OneGonAdicIndependentModel
