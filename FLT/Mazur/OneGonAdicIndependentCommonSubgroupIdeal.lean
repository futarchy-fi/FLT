/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.OneGonAdicIndependentCommonSubgroup
public import FLT.Mazur.OneGonAdicIndependentCommonIdeal

/-!
# Full ideals of the bundled independent common subgroups

The compatible finite subgroups retain the original whole-curve ideal
comparison over the literal common finite ring and after every further test.
No radical, reducedness, flatness, or order-invertibility assumption is used.
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

/-- The left common subgroup has the entire original stage-embedding ideal. -/
theorem commonFiniteSubgroupLeft_ideal :
    (commonFiniteSubgroupLeft I t ht n s u i j hs b hb hφs).ideal =
      (stageEmbedding I t ht n s (commonLeft I t ht n s u i j) hs).left.ker :=
  stageFiniteSubgroup_ideal I t ht n s (commonLeft I t ht n s u i j)
    (commonFactorLeft I t ht n s b u j)
    (refinedFactor_inclusion I t ht n s (commonToLeft I t ht n s u i j) b hb) hs hφs

/-- The right common subgroup has the entire original stage-embedding ideal. -/
theorem commonFiniteSubgroupRight_ideal :
    (commonFiniteSubgroupRight I t ht n s u i j hu c hc hφu).ideal =
      (stageEmbedding I t ht n u (commonRight I t ht n s u i j) hu).left.ker :=
  stageFiniteSubgroup_ideal I t ht n u (commonRight I t ht n s u i j)
    (commonFactorRight I t ht n s (i := i) u j c)
    (refinedFactor_inclusion I t ht n u (commonToRight I t ht n s u i j) c hc) hu hφu

/-- The constructed common comparison identifies the whole ideals of the bundled subgroups. -/
theorem commonFiniteSubgroup_ideal :
    (commonFiniteSubgroupLeft I t ht n s u i j hs b hb hφs).ideal =
      (commonFiniteSubgroupRight I t ht n s u i j hu c hc hφu).ideal.comap
        (commonCurveIso I t ht n s u i j hs hu).hom.curve.left :=
  (commonFiniteSubgroupLeft_ideal I t ht n s u i j hs b hb hφs).trans
    ((common_embedding_ideal I t ht n s u i j hs hu hφu).trans
      (congrArg (fun a => a.comap (commonCurveIso I t ht n s u i j hs hu).hom.curve.left)
        (commonFiniteSubgroupRight_ideal I t ht n s u i j hu c hc hφu)).symm)

/-- All further tests retain every infinitesimal multiplicity of the common subgroup ideals. -/
theorem commonFiniteSubgroup_ideal_baseChange {T : Scheme}
    (v : T ⟶ (stageCurve I t ht n s (commonLeft I t ht n s u i j) hs).curve.left) :
    (commonFiniteSubgroupLeft I t ht n s u i j hs b hb hφs).ideal.comap v =
      (commonFiniteSubgroupRight I t ht n s u i j hu c hc hφu).ideal.comap
        (v ≫ (commonCurveIso I t ht n s u i j hs hu).hom.curve.left) := by
  rw [commonFiniteSubgroup_ideal I t ht n s u i j hs hu b hb c hc hφs hφu,
    Scheme.IdealSheafData.comap_comp]

end FLT.Mazur.OneGonAdicIndependentModel
