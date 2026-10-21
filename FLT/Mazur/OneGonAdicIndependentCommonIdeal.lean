/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.OneGonAdicIndependentCommonEmbedding
public import Mathlib.AlgebraicGeometry.IdealSheaf.Functorial

/-!
# Full ideals over the common independent coefficient ring

The constructed equality of intrinsic full embeddings gives a Cartesian square.
Closed immersions therefore retain their whole ideal sheaves over the finite
common ring itself and after every further test base change.
-/

@[expose] public noncomputable section
open CategoryTheory Limits AlgebraicGeometry
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

/-- The finite common comparison retains the entire subgroup ideal, including nilpotents. -/
theorem common_embedding_ideal
    (hφ : Function.Surjective (OneGonFiniteCoefficientCoordinates.modelCoordinates t 1
      (canonicalCoordinates I t ht n) u)) :
    (stageEmbedding I t ht n s (commonLeft I t ht n s u i j) hs).left.ker =
      (stageEmbedding I t ht n u (commonRight I t ht n s u i j) hu).left.ker.comap
        (commonCurveIso I t ht n s u i j hs hu).hom.curve.left := by
  let f := ((stageCharacterIso I t ht n s (commonLeft I t ht n s u i j)).hom ≫
    stageEmbedding I t ht n s (commonLeft I t ht n s u i j) hs).left
  let g := ((stageCharacterIso I t ht n u (commonRight I t ht n s u i j)).hom ≫
    stageEmbedding I t ht n u (commonRight I t ht n s u i j) hu).left
  let e := (commonCurveIso I t ht n s u i j hs hu).hom.curve.left
  let _ := stageEmbedding_isClosedImmersion I t ht n u
    (commonRight I t ht n s u i j) hu hφ
  let _ : IsClosedImmersion g := by
    dsimp only [g, Over.comp_left]
    infer_instance
  let _ : IsIso e := inferInstanceAs
    (IsIso ((GeneralizedEllipticCurve.forgetCurve.mapIso
      (commonCurveIso I t ht n s u i j hs hu)).hom.left))
  have q : IsPullback f (𝟙 _) e g := by
    apply IsPullback.of_vert_isIso
    refine ⟨?_⟩
    exact (congrArg (fun k => k.left)
      (common_intrinsic_embedding_square I t ht n s u i j hs hu)).trans
        (Category.id_comp g).symm
  have hi : f.ker = g.ker.comap e := by
    rw [← q.isoPullback_hom_fst, Scheme.Hom.ker_comp_of_isIso]
    exact Scheme.IdealSheafData.ker_fst_of_isClosedImmersion _ _
  simpa only [f, g, e, Over.comp_left, Scheme.Hom.ker_comp_of_isIso] using hi

/-- Every further test retains the full common-stage ideal comparison. -/
theorem common_embedding_ideal_baseChange
    (hφ : Function.Surjective (OneGonFiniteCoefficientCoordinates.modelCoordinates t 1
      (canonicalCoordinates I t ht n) u))
    {T : Scheme} (v : T ⟶ (stageCurve I t ht n s (commonLeft I t ht n s u i j) hs).curve.left) :
    (stageEmbedding I t ht n s (commonLeft I t ht n s u i j) hs).left.ker.comap v =
      (stageEmbedding I t ht n u (commonRight I t ht n s u i j) hu).left.ker.comap
        (v ≫ (commonCurveIso I t ht n s u i j hs hu).hom.curve.left) := by
  rw [common_embedding_ideal I t ht n s u i j hs hu hφ,
    Scheme.IdealSheafData.comap_comp]

end FLT.Mazur.OneGonAdicIndependentModel
