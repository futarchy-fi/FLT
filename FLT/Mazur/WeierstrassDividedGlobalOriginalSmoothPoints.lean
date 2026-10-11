/-
Copyright (c) 2026 krandder. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: krandder
-/
module

public import FLT.Mazur.WeierstrassDividedGlobalActionSmooth

/-!
# The whole action retains all original smooth points

Every original smooth scheme-valued point embeds injectively. Its action
is precisely the original addition, including over nonflat test schemes.
-/

@[expose] public noncomputable section
open AlgebraicGeometry CategoryTheory Limits
namespace FLT.Mazur.WeierstrassDividedDepth
open WeierstrassIntegralChart
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
universe u
variable {R : Type u} [CommRing R] [IsDomain R] [IsBezout R]
  {W : WeierstrassCurve R} {π : R} (hπ : π ≠ 0) {start n : ℕ}
  (data : (i : Fin (n + 1)) → Data W π (start + i.val))

variable (j : ℕ) (hj : j ≤ n)

/-- Smooth scheme-valued inputs retain exactly their original sum at every depth. -/
theorem finiteGlobalPointAction_smoothEmbedding {T : Scheme.{u}}
    (a b : T ⟶ (integralSmoothOpen W).toScheme)
    (h : a ≫ integralSmoothStructure W = b ≫ integralSmoothStructure W) :
    finiteGlobalPointAction hπ data j hj a (b ≫ finiteGlobalSmoothEmbedding hπ data j hj)
        (by rw [Category.assoc, finiteGlobalSmoothEmbedding_structure]; exact h) =
      smoothPairPointAddition W a b h ≫ finiteGlobalSmoothEmbedding hπ data j hj := by
  have he := congrArg (fun f => pullback.lift a b h ≫ f)
    (finiteGlobalAction_originalSmooth hπ data j hj)
  rw [← Category.assoc] at he
  have hp : pullback.lift a b h ≫ finiteGlobalOriginalSmoothPair hπ data j hj =
      pullback.lift a (b ≫ finiteGlobalSmoothEmbedding hπ data j hj)
        (by rw [Category.assoc, finiteGlobalSmoothEmbedding_structure]; exact h) := by
    apply pullback.hom_ext <;>
      simp only [Category.assoc, finiteGlobalOriginalSmoothPair_fst,
        finiteGlobalOriginalSmoothPair_snd, pullback.lift_fst, pullback.lift_snd,
        pullback.lift_snd_assoc]
  rw [hp] at he
  simpa only [finiteGlobalPointAction, finiteGlobalOriginalSmoothAction,
    smoothPairPointAddition, Category.assoc] using he

/-- Distinct original smooth points stay distinct on the actual finite model. -/
theorem finiteGlobalSmoothEmbedding_points_injective (T : Scheme.{u}) :
    Function.Injective (fun a : T ⟶ (integralSmoothOpen W).toScheme =>
      a ≫ finiteGlobalSmoothEmbedding hπ data j hj) := by
  intro a b h
  exact (cancel_mono (finiteGlobalSmoothEmbedding hπ data j hj)).mp h

/-- The original zero point embeds with its original coefficient morphism. -/
def finiteGlobalZeroPoint (T : Over (Spec (.of R))) :
    T.left ⟶ finiteGlobalModel hπ data j hj :=
  T.hom ≫ integralSmoothZero W ≫ finiteGlobalSmoothEmbedding hπ data j hj

/-- The embedded zero is a point over the original coefficient spectrum. -/
@[reassoc] theorem finiteGlobalZeroPoint_structure (T : Over (Spec (.of R))) :
    finiteGlobalZeroPoint hπ data j hj T ≫ finiteGlobalStructure hπ data j hj = T.hom := by
  rw [finiteGlobalZeroPoint, Category.assoc, Category.assoc,
    finiteGlobalSmoothEmbedding_structure, integralSmoothZero_structure, Category.comp_id]

end FLT.Mazur.WeierstrassDividedDepth
