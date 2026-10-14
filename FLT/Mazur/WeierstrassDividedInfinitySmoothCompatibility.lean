/-
Copyright (c) 2026 krandder. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: krandder
-/
module

public import FLT.Mazur.EllipticResolvedIdentityChart

/-!
# The retained infinity chart is the original smooth coefficient embedding

At every finite stage, including stage zero, the two independently constructed
maps agree on their full coefficient and integral projections. In particular,
the actual resolved identity chart covers the entire original infinity chart.
-/

@[expose] public noncomputable section
open AlgebraicGeometry CategoryTheory Limits IsLocalRing
namespace FLT.Mazur.WeierstrassDividedDepth
open WeierstrassIntegralChart
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
universe u
variable {R : Type u} [CommRing R] [IsDomain R] [IsBezout R] [IsLocalRing R]
  {W : WeierstrassCurve R} {π : R} (hπ : π ≠ 0) {start n depth : ℕ}
  (data : (i : Fin (n + 1)) → Data W π (start + i.val))
  (D : SplitNodeDepth W π depth) (hd : 0 < depth) (j : ℕ) (hj : j ≤ n)
local notation "F" => ResidueField R
local notation "q" => Spec.map (CommRingCat.ofHom (algebraMap R F))
local notation "f" => finiteGlobalStructure hπ data j hj
local notation "e" => infinityResidueSmoothIso D hd
local notation "c" => infinityLaurentChart hπ data D hd j hj

/-- The infinity parametrization retains the integral smooth embedding at every depth. -/
@[reassoc] theorem infinityLaurentChart_smooth_projection :
    c ≫ pullback.snd q f = (e).hom ≫ originalSmoothCoefficientMap F W ≫
      finiteGlobalSmoothEmbedding hπ data j hj := by
  let H := finiteGlobalSmoothEmbedding_isPullback hπ data j hj
  let g := c ≫ pullback.snd q f
  let a := (e).hom ≫ originalSmoothCoefficientMap F W
  have hw : a ≫ (integralSmoothOpen W).ι =
      g ≫ finiteGlobalContraction hπ data j hj := by
    dsimp only [a, g]
    rw [Category.assoc, originalSmoothCoefficientMap_inclusion,
      infinityResidueSmoothIso_contraction, Category.assoc, infinityLaurentChart_toCurve]
  have hl : H.lift a g hw = a := by
    simpa only [Category.comp_id] using H.lift_fst a g hw
  have he := H.lift_snd a g hw
  rw [hl] at he
  exact he.symm

/-- The full infinity Laurent morphism is the actual original smooth coefficient embedding. -/
theorem infinityLaurentChart_eq_smooth_embedding :
    c = (e).hom ≫ finiteGlobalSmoothCoefficientEmbedding F hπ data j hj := by
  apply (IsPullback.of_hasPullback q f).hom_ext
  · rw [infinityLaurentChart_structure, Category.assoc,
      finiteGlobalSmoothCoefficientEmbedding_structure, infinityResidueSmoothIso_structure]
  · rw [infinityLaurentChart_smooth_projection, Category.assoc,
      finiteGlobalSmoothCoefficientEmbedding_projection]

variable {K : Type u} [Field K] (A : ValuationSubring K)
  {V : WeierstrassCurve A} {ϖ : A} (E : SplitNodeDepth V ϖ depth)

/-- The actual resolved identity chart is the retained original infinity Laurent chart. -/
theorem resolvedIdentityChart_eq_infinity :
    resolvedIdentityChart A E = infinityLaurentChart E.uniformizer_ne_zero
      (splitResolutionData A E) E E.depth_pos (depth / 2) (le_refl _) :=
  (infinityLaurentChart_eq_smooth_embedding E.uniformizer_ne_zero
    (splitResolutionData A E) E E.depth_pos (depth / 2) (le_refl _)).symm

/-- The identity torus covers the entire original infinity tensor chart, also at depth one. -/
theorem resolvedIdentityChart_range_infinity :
    Set.range (resolvedIdentityChart A E) =
      Set.range (finiteInfinityTensorChart E.uniformizer_ne_zero
        (splitResolutionData A E) (ResidueField A) (depth / 2) (le_refl _)) := by
  rw [resolvedIdentityChart_eq_infinity, infinityLaurentChart_range]

end FLT.Mazur.WeierstrassDividedDepth
