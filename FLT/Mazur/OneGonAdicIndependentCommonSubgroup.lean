/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.OneGonAdicIndependentCommonFactors
public import FLT.Mazur.OneGonAdicIndependentFiniteSubgroup
public import FLT.Mazur.CompatibleSubgroupIso

/-!
# Compatible finite subgroups over the actual common coefficient ring

The two arbitrary supplied stages refine to finite subgroups over their
literal common ring. Their intrinsic character sources agree, and the full
arithmetic curve comparison preserves the entire subgroup embedding.
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

/-- The left supplied subgroup refined to the literal common finite ring. -/
def commonFiniteSubgroupLeft :
    GeneralizedEllipticCurve.FiniteSubgroup (S := Spec (.of (commonBase I t ht n s u i j)))
      (stageCurve I t ht n s (commonLeft I t ht n s u i j) hs) n :=
  stageFiniteSubgroup I t ht n s (commonLeft I t ht n s u i j)
    (commonFactorLeft I t ht n s b u j)
    (refinedFactor_inclusion I t ht n s (commonToLeft I t ht n s u i j) b hb) hs hφs

/-- The right supplied subgroup refined to that same common finite ring. -/
def commonFiniteSubgroupRight :
    GeneralizedEllipticCurve.FiniteSubgroup (S := Spec (.of (commonBase I t ht n s u i j)))
      (stageCurve I t ht n u (commonRight I t ht n s u i j) hu) n :=
  stageFiniteSubgroup I t ht n u (commonRight I t ht n s u i j)
    (commonFactorRight I t ht n s (i := i) u j c)
    (refinedFactor_inclusion I t ht n u (commonToRight I t ht n s u i j) c hc) hu hφu

/-- The whole left subgroup map is its actual intrinsic common-stage embedding. -/
theorem commonFiniteSubgroupLeft_curveMap :
    (commonFiniteSubgroupLeft I t ht n s u i j hs b hb hφs).curveMap =
      (stageCharacterIso I t ht n s (commonLeft I t ht n s u i j)).hom ≫
        stageEmbedding I t ht n s (commonLeft I t ht n s u i j) hs := by
  exact stageFiniteSubgroup_curveMap I t ht n s (commonLeft I t ht n s u i j)
    (commonFactorLeft I t ht n s b u j)
    (refinedFactor_inclusion I t ht n s (commonToLeft I t ht n s u i j) b hb) hs hφs

/-- The whole right subgroup map is its actual intrinsic common-stage embedding. -/
theorem commonFiniteSubgroupRight_curveMap :
    (commonFiniteSubgroupRight I t ht n s u i j hu c hc hφu).curveMap =
      (stageCharacterIso I t ht n u (commonRight I t ht n s u i j)).hom ≫
        stageEmbedding I t ht n u (commonRight I t ht n s u i j) hu := by
  exact stageFiniteSubgroup_curveMap I t ht n u (commonRight I t ht n s u i j)
    (commonFactorRight I t ht n s (i := i) u j c)
    (refinedFactor_inclusion I t ht n u (commonToRight I t ht n s u i j) c hc) hu hφu

/-- The constructed full curve comparison identifies the two actual finite subgroups. -/
def commonFiniteSubgroupIso : GeneralizedEllipticCurve.FiniteSubgroup.CompatibleIso
    (S := Spec (.of (commonBase I t ht n s u i j)))
    (commonFiniteSubgroupLeft I t ht n s u i j hs b hb hφs)
    (commonFiniteSubgroupRight I t ht n s u i j hu c hc hφu) where
  curve := commonCurveIso I t ht n s u i j hs hu
  subgroup := Iso.refl (model (commonBase I t ht n s u i j) (ZMod n))
  isMonHom := inferInstanceAs (IsMonHom (𝟙 (model (commonBase I t ht n s u i j) (ZMod n))))
  compatible := (congrArg (fun f => f ≫ (commonCurveIso I t ht n s u i j hs hu).hom.curve)
      (commonFiniteSubgroupLeft_curveMap I t ht n s u i j hs b hb hφs)).trans
        ((common_intrinsic_embedding_square I t ht n s u i j hs hu).trans
          ((commonFiniteSubgroupRight_curveMap I t ht n s u i j hu c hc hφu).symm.trans
            (Category.id_comp
              (commonFiniteSubgroupRight I t ht n s u i j hu c hc hφu).curveMap).symm))

end FLT.Mazur.OneGonAdicIndependentModel
