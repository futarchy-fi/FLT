/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.OneGonAdicIndependentCommonSubgroup
public import FLT.Mazur.OneGonAdicIndependentSubgroupRecovery

/-!
# Recovery coherence of the actual common finite subgroups

The compatible comparison over the common finite ring recovers to the same
canonical subgroup. This is an equality of bundled compatible isomorphisms,
retaining both the full generalized curve and the actual character source.
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

/-- Compatible recovery of the left actual common subgroup. -/
def commonFiniteSubgroupLeftRecoveryIso :=
  stageFiniteSubgroupRecoveryIso I t ht n s (commonLeft I t ht n s u i j)
    (commonFactorLeft I t ht n s b u j)
    (refinedFactor_inclusion I t ht n s (commonToLeft I t ht n s u i j) b hb) hs hφs

/-- Compatible recovery of the right actual common subgroup. -/
def commonFiniteSubgroupRightRecoveryIso :=
  stageFiniteSubgroupRecoveryIso I t ht n u (commonRight I t ht n s u i j)
    (commonFactorRight I t ht n s (i := i) u j c)
    (refinedFactor_inclusion I t ht n u (commonToRight I t ht n s u i j) c hc) hu hφu

/-- The actual common comparison commutes with both bundled subgroup recoveries. -/
theorem commonFiniteSubgroupIso_recovery :
    (commonFiniteSubgroupLeftRecoveryIso I t ht n s u i j hs b hb hφs).trans
      ((commonFiniteSubgroupIso I t ht n s u i j hs hu b hb c hc hφs hφu).baseChange
        (baseMap (commonBase I t ht n s u i j) R)) =
      commonFiniteSubgroupRightRecoveryIso I t ht n s u i j hu c hc hφu := by
  apply GeneralizedEllipticCurve.FiniteSubgroup.CompatibleIso.ext
  · apply Iso.ext
    exact commonCurveIso_recovery I t ht n s u i j hs hu
  · apply Iso.ext
    change (overIso (commonBase I t ht n s u i j) R (ZMod n)).hom ≫
      (Over.pullback (baseMap (commonBase I t ht n s u i j) R)).map
        (𝟙 (model (commonBase I t ht n s u i j) (ZMod n))) =
      (overIso (commonBase I t ht n s u i j) R (ZMod n)).hom
    exact (congrArg
      (fun f => (overIso (commonBase I t ht n s u i j) R (ZMod n)).hom ≫ f)
      ((Over.pullback (baseMap (commonBase I t ht n s u i j) R)).map_id
        (model (commonBase I t ht n s u i j) (ZMod n)))).trans (Category.comp_id _)

end FLT.Mazur.OneGonAdicIndependentModel
