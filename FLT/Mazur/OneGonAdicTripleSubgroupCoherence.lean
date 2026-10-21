/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.OneGonAdicTripleStage
public import FLT.Mazur.OneGonAdicSharedSubgroupCoherence

/-!
# The actual three-presentation subgroup cocycle over the literal supremum

For three independent supports and three independently supplied smooth stages,
their literal triple supremum carries actual refinements of all three finite
subgroups. The constructed compatible comparisons satisfy the full cocycle.
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

/-- Three supplied presentations are coherently identified over their literal triple ring. -/
theorem tripleFiniteSubgroupIso_trans :
    let K := tripleBase I t ht n s u v i j k
    let hS := base_le_triple_first I t ht n s u v i j k
    let hU := base_le_triple_second I t ht n s u v i j k
    let hV := base_le_triple_third I t ht n s u v i j k
    let hi := stage_le_triple_first I t ht n s u v i j k
    let hj := stage_le_triple_second I t ht n s u v i j k
    let hk := stage_le_triple_third I t ht n s u v i j k
    (sharedFiniteSubgroupIso I t ht n s u K hS hU hs hu i j hi hj b hb c hc hφs hφu).trans
      (sharedFiniteSubgroupIso I t ht n u v K hU hV hu hv j k hj hk c hc d hd hφu hφv) =
        sharedFiniteSubgroupIso I t ht n s v K hS hV hs hv i k hi hk b hb d hd hφs hφv := by
  dsimp only
  apply sharedFiniteSubgroupIso_trans

end FLT.Mazur.OneGonAdicIndependentModel
