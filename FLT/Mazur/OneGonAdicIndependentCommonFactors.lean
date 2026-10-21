/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.OneGonAdicIndependentCommonEmbedding
public import FLT.Mazur.OneGonAdicIndependentStageRefinement

/-!
# Actual independent smooth factors over the common finite ring

The whole-embedding equality identifies the two supplied smooth-stage factors
on their intrinsic character source. The comparison and recovery are constructed,
including in characteristics dividing the subgroup order.
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
  (i : (CoefficientStage (base I t ht n s))ᵒᵖ)
  (j : (CoefficientStage (base I t ht n u))ᵒᵖ)
  (hs : complementaryInverse I t ht ∈ s) (hu : complementaryInverse I t ht ∈ u)

/-- Full embeddings determine smooth factors under a generalized-curve comparison. -/
theorem smoothFactor_square_of_fullEmbedding {S : Scheme}
    {E F : GeneralizedEllipticCurve S} (e : E ≅ F)
    {X : Over S} (f : X ⟶ E.group) (g : X ⟶ F.group)
    (h : (f ≫ E.inclusion) ≫ e.hom.curve = g ≫ F.inclusion) :
    f ≫ e.hom.group = g := by
  let _ : Mono F.inclusion := by
    dsimp [GeneralizedEllipticCurve.inclusion, curveSmoothInclusion]
    infer_instance
  apply (cancel_mono F.inclusion).mp
  rw [Category.assoc, ← e.hom.inclusion, ← Category.assoc]
  exact h

/-- The full finite-base embedding equality identifies its two intrinsic smooth factors. -/
theorem common_intrinsic_factors_square
    (f : stageCarrier I t ht n s (commonLeft I t ht n s u i j) ⟶
      (stageCurve I t ht n s (commonLeft I t ht n s u i j) hs).group)
    (g : stageCarrier I t ht n u (commonRight I t ht n s u i j) ⟶
      (stageCurve I t ht n u (commonRight I t ht n s u i j) hu).group)
    (hf : f ≫ (stageCurve I t ht n s (commonLeft I t ht n s u i j) hs).inclusion =
      stageEmbedding I t ht n s (commonLeft I t ht n s u i j) hs)
    (hg : g ≫ (stageCurve I t ht n u (commonRight I t ht n s u i j) hu).inclusion =
      stageEmbedding I t ht n u (commonRight I t ht n s u i j) hu) :
    ((stageCharacterIso I t ht n s (commonLeft I t ht n s u i j)).hom ≫ f) ≫
      (commonCurveIso I t ht n s u i j hs hu).hom.group =
    (stageCharacterIso I t ht n u (commonRight I t ht n s u i j)).hom ≫ g := by
  apply smoothFactor_square_of_fullEmbedding (commonCurveIso I t ht n s u i j hs hu)
  change (((stageCharacterIso I t ht n s (commonLeft I t ht n s u i j)).hom ≫ f) ≫
      (stageCurve I t ht n s (commonLeft I t ht n s u i j) hs).inclusion) ≫ _ =
    ((stageCharacterIso I t ht n u (commonRight I t ht n s u i j)).hom ≫ g) ≫
      (stageCurve I t ht n u (commonRight I t ht n s u i j) hu).inclusion
  rw [Category.assoc (stageCharacterIso I t ht n s (commonLeft I t ht n s u i j)).hom,
    Category.assoc (stageCharacterIso I t ht n u (commonRight I t ht n s u i j)).hom, hf, hg]
  exact common_intrinsic_embedding_square I t ht n s u i j hs hu

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

/-- Lift the actual left refined factor into its common-stage smooth group. -/
irreducible_def commonSmoothFactorLeft :=
  stageFactor I t ht n s (commonLeft I t ht n s u i j)
    (commonFactorLeft I t ht n s b u j)
    (refinedFactor_inclusion I t ht n s (commonToLeft I t ht n s u i j) b hb) hs

/-- Lift the actual right refined factor into the other common-stage smooth group. -/
irreducible_def commonSmoothFactorRight :=
  stageFactor I t ht n u (commonRight I t ht n s u i j)
    (commonFactorRight I t ht n s (i := i) u j c)
    (refinedFactor_inclusion I t ht n u (commonToRight I t ht n s u i j) c hc) hu

/-- Independently supplied smooth stages give the same subgroup over the common finite ring. -/
theorem common_refined_factors_square :
    ((stageCharacterIso I t ht n s (commonLeft I t ht n s u i j)).hom ≫
      commonSmoothFactorLeft I t ht n s u i j hs b hb) ≫
        (commonCurveIso I t ht n s u i j hs hu).hom.group =
    (stageCharacterIso I t ht n u (commonRight I t ht n s u i j)).hom ≫
      commonSmoothFactorRight I t ht n s u i j hu c hc := by
  apply common_intrinsic_factors_square I t ht n s u i j hs hu
  · rw [commonSmoothFactorLeft_def]
    exact stageFactor_inclusion I t ht n s (commonLeft I t ht n s u i j) _ _ hs
  · rw [commonSmoothFactorRight_def]
    exact stageFactor_inclusion I t ht n u (commonRight I t ht n s u i j) _ _ hu

end FLT.Mazur.OneGonAdicIndependentModel
