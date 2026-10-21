/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.OneGonAdicSharedSubgroup
public import FLT.Mazur.OneGonAdicSharedEmbedding

/-!
# Compatible comparison of actual independently supplied subgroups

Two supplied smooth stages refine to the shared finite ring. The proved full
embedding square identifies their actual finite subgroups, with identity source map.
-/

@[expose] public noncomputable section
open CategoryTheory AlgebraicGeometry
namespace FLT.Mazur.OneGonAdicIndependentModel
open Approximation OneGonAdicCharacterTower OneGonSmoothing CharacterSchemeBaseChange
open ArithmeticOneGonGeneralizedCurve WeierstrassIntegralChart
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
variable {R : Type} [CommRing R] (I : Ideal R) [IsAdicComplete I R]
  (t : R) (ht : t ∈ I) (n : ℕ) [NeZero n] (s u : Set R)
  (K : Subalgebra ℤ R) [Algebra.FiniteType ℤ K]
  (hS : base I t ht n s ≤ K) (hU : base I t ht n u ≤ K)
  (hs : complementaryInverse I t ht ∈ s) (hu : complementaryInverse I t ht ∈ u)

variable (i : (CoefficientStage (base I t ht n s))ᵒᵖ)
  (j : (CoefficientStage (base I t ht n u))ᵒᵖ)
  (hi : stageBase I t ht n s i ≤ K) (hj : stageBase I t ht n u j ≤ K)
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

/-- Full compatible comparison of the two actually refined supplied finite subgroups. -/
def sharedFiniteSubgroupIso : GeneralizedEllipticCurve.FiniteSubgroup.CompatibleIso
    (S := Spec (.of K))
    (sharedFiniteSubgroup I t ht n s K hS i hi b hb hs hφs)
    (sharedFiniteSubgroup I t ht n u K hU j hj c hc hu hφu) where
  curve := sharedCurveIso I t ht n s u K hS hU hs hu
  subgroup := Iso.refl (model K (ZMod n))
  isMonHom := inferInstanceAs (IsMonHom (𝟙 (model K (ZMod n))))
  compatible := (congrArg (fun f => f ≫ (sharedCurveIso I t ht n s u K hS hU hs hu).hom.curve)
      (sharedFiniteSubgroup_curveMap I t ht n s K hS i hi b hb hs hφs)).trans
        ((shared_intrinsic_embedding_square I t ht n s u K hS hU hs hu).trans
          ((sharedFiniteSubgroup_curveMap I t ht n u K hU j hj c hc hu hφu).symm.trans
            (Category.id_comp
              (sharedFiniteSubgroup I t ht n u K hU j hj c hc hu hφu).curveMap).symm))

/-- The shared comparison commutes with recovery as a bundled compatible subgroup isomorphism. -/
theorem sharedFiniteSubgroupIso_recovery :
    (sharedFiniteSubgroupRecoveryIso I t ht n s K hS i hi b hb hs hφs).trans
      ((sharedFiniteSubgroupIso I t ht n s u K hS hU hs hu i j hi hj b hb c hc hφs hφu).baseChange
        (baseMap K R)) =
      sharedFiniteSubgroupRecoveryIso I t ht n u K hU j hj c hc hu hφu := by
  apply GeneralizedEllipticCurve.FiniteSubgroup.CompatibleIso.ext
  · apply Iso.ext
    exact sharedCurveIso_recovery I t ht n s u K hS hU hs hu
  · apply Iso.ext
    change (overIso K R (ZMod n)).hom ≫
      (Over.pullback (baseMap K R)).map (𝟙 (model K (ZMod n))) =
        (overIso K R (ZMod n)).hom
    rw [(Over.pullback (baseMap K R)).map_id, Category.comp_id]

end FLT.Mazur.OneGonAdicIndependentModel
