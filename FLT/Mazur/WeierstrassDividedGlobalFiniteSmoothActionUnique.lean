/-
Copyright (c) 2026 krandder. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: krandder
-/
module

public import FLT.Mazur.WeierstrassDividedGlobalFiniteActionProduct

/-!
# Unique action lifts over the original unchanged smooth locus

Every common-source map whose contraction is an original smooth point is the
unique retained smooth lift. Thus local action formulas agree on all overlaps
whose output contracts into the original smooth open. Exceptional output loci
still require their own chart formulas and overlap calculations.
-/

@[expose] public noncomputable section

open AlgebraicGeometry CategoryTheory

namespace FLT.Mazur.WeierstrassDividedDepth

open WeierstrassIntegralChart
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true

variable {R : Type*} [CommRing R] [IsDomain R] [IsBezout R]
  {W : WeierstrassCurve R} {π : R} (hπ : π ≠ 0) {start n : ℕ}
  (data : (i : Fin (n + 1)) → Data W π (start + i.val)) (j : ℕ) (hj : j ≤ n)

/-- Any map above an original smooth point is exactly its original retained embedding. -/
theorem finiteGlobal_eq_smoothEmbedding {T : Scheme}
    (s : T ⟶ (integralSmoothOpen W).toScheme) (f : T ⟶ finiteGlobalModel hπ data j hj)
    (hf : f ≫ finiteGlobalContraction hπ data j hj = s ≫ (integralSmoothOpen W).ι) :
    f = s ≫ finiteGlobalSmoothEmbedding hπ data j hj := by
  let H := finiteGlobalSmoothEmbedding_isPullback hπ data j hj
  have hl : H.lift s f hf.symm = s := by
    simpa only [Category.comp_id] using H.lift_fst s f hf.symm
  have he := H.lift_snd s f hf.symm
  simpa only [hl] using he.symm

/-- Two local lifts agree whenever their common contraction has an original smooth presentation. -/
theorem finiteGlobal_smooth_output_hom_ext {T : Scheme}
    (s : T ⟶ (integralSmoothOpen W).toScheme) (f g : T ⟶ finiteGlobalModel hπ data j hj)
    (hf : f ≫ finiteGlobalContraction hπ data j hj = s ≫ (integralSmoothOpen W).ι)
    (hg : g ≫ finiteGlobalContraction hπ data j hj = s ≫ (integralSmoothOpen W).ι) :
    f = g :=
  (finiteGlobal_eq_smoothEmbedding hπ data j hj s f hf).trans
    (finiteGlobal_eq_smoothEmbedding hπ data j hj s g hg).symm

/-- A whole-model action lift must recover the constructed action on original smooth inputs. -/
theorem finiteGlobalAction_originalSmooth_unique
    (f : finiteGlobalActionProduct hπ data j hj ⟶ finiteGlobalModel hπ data j hj)
    (hf : f ≫ finiteGlobalContraction hπ data j hj =
      finiteGlobalActionInput hπ data j hj ≫ leftSmoothFactorAddition W) :
    finiteGlobalOriginalSmoothPair hπ data j hj ≫ f =
      finiteGlobalOriginalSmoothAction hπ data j hj := by
  apply finiteGlobal_eq_smoothEmbedding hπ data j hj (smoothFactorAddition W)
  rw [Category.assoc, hf, finiteGlobalOriginalSmoothPair_input_assoc,
    smoothFactorsToLeftSmooth_addition]

end FLT.Mazur.WeierstrassDividedDepth
