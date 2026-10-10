/-
Copyright (c) 2026 krandder. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: krandder
-/
module

public import FLT.Mazur.WeierstrassDividedGlobalFiniteSmoothOpen
public import FLT.Mazur.WeierstrassDividedGlobalFiniteStep

/-!
# Retain the original smooth scheme at every finite global depth

The inverse comparison embeds the complete original relative smooth scheme,
with its original structure map and full contraction pullback. Every actual
finite global step carries this embedding to its predecessor.
-/

@[expose] public noncomputable section
open AlgebraicGeometry CategoryTheory
namespace FLT.Mazur.WeierstrassDividedDepth
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
variable {R : Type*} [CommRing R] [IsDomain R] [IsBezout R]
  {W : WeierstrassCurve R} {π : R} (hπ : π ≠ 0) {start n : ℕ}
  (data : (i : Fin (n + 1)) → Data W π (start + i.val)) (j : ℕ) (hj : j ≤ n)
open WeierstrassIntegralChart

/-- The full original relative smooth scheme embedded in the actual finite global model. -/
def finiteGlobalSmoothEmbedding :
    (integralSmoothOpen W).toScheme ⟶ finiteGlobalModel hπ data j hj :=
  SchemeUnchangedOpen.lift (finiteGlobalContraction hπ data j hj) (integralSmoothOpen W).ι
    (by
      rw [Scheme.Opens.opensRange_ι]
      exact finiteGlobal_originalSmooth_isIso hπ data j hj)

instance finiteGlobalSmoothEmbedding_isOpenImmersion :
    IsOpenImmersion (finiteGlobalSmoothEmbedding hπ data j hj) := by
  unfold finiteGlobalSmoothEmbedding
  infer_instance

/-- The retained smooth scheme contracts by precisely its original open inclusion. -/
@[reassoc] theorem finiteGlobalSmoothEmbedding_contraction :
    finiteGlobalSmoothEmbedding hπ data j hj ≫ finiteGlobalContraction hπ data j hj =
      (integralSmoothOpen W).ι := SchemeUnchangedOpen.lift_comp _ _ _

/-- The embedding is the entire pullback of the original smooth open. -/
theorem finiteGlobalSmoothEmbedding_isPullback :
    IsPullback (𝟙 _) (finiteGlobalSmoothEmbedding hπ data j hj)
      (integralSmoothOpen W).ι (finiteGlobalContraction hπ data j hj) :=
  SchemeUnchangedOpen.lift_isPullback _ _ _

/-- There are no other points over the original relative smooth locus. -/
theorem finiteGlobalSmoothEmbedding_range :
    Set.range (finiteGlobalSmoothEmbedding hπ data j hj) =
      finiteGlobalContraction hπ data j hj ⁻¹' (integralSmoothOpen W : Set _) := by
  have h := IsOpenImmersion.image_preimage_eq_preimage_image_of_isPullback
    (finiteGlobalSmoothEmbedding_isPullback hπ data j hj) ⊤
  simpa using congrArg SetLike.coe h

/-- The retained smooth scheme keeps exactly the original base structure morphism. -/
@[reassoc] theorem finiteGlobalSmoothEmbedding_structure :
    finiteGlobalSmoothEmbedding hπ data j hj ≫ finiteGlobalStructure hπ data j hj =
      integralSmoothStructure W := by
  rw [finiteGlobalStructure, finiteGlobalSmoothEmbedding_contraction_assoc]

/-- The retained full original smooth open is smooth over the coefficient base. -/
instance finiteGlobalSmoothEmbedding_structure_smooth :
    Smooth (finiteGlobalSmoothEmbedding hπ data j hj ≫ finiteGlobalStructure hπ data j hj) := by
  rw [finiteGlobalSmoothEmbedding_structure]
  infer_instance

/-- Every actual global step retains the complete original smooth embedding. -/
@[reassoc] theorem finiteGlobalSmoothEmbedding_step (hnext : j + 1 ≤ n) :
    finiteGlobalSmoothEmbedding hπ data (j + 1) hnext ≫ finiteGlobalStep hπ data j hnext =
      finiteGlobalSmoothEmbedding hπ data j (Nat.le_of_succ_le hnext) := by
  apply SchemeUnchangedOpen.lift_unique
  rw [Category.assoc, finiteGlobalStep_contraction, finiteGlobalSmoothEmbedding_contraction]

end FLT.Mazur.WeierstrassDividedDepth
