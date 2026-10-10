/-
Copyright (c) 2026 krandder. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: krandder
-/
module

public import FLT.Mazur.WeierstrassDividedAdjacentRetainedTensorIntersection
public import FLT.Mazur.WeierstrassSuccessiveXResidueConicIntegralBoundary

/-!
# The full normalized adjacent intersection

The whole conic incidence open, with its original conic inclusion and inverse
horizontal transition, is the complete intersection of the retained charts.
-/

@[expose] public noncomputable section
open AlgebraicGeometry CategoryTheory IsLocalRing Limits
namespace FLT.Mazur.WeierstrassDividedDepth
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
universe u
variable {R : Type u} [CommRing R] [IsDomain R] [IsBezout R] [IsLocalRing R]
  {W : WeierstrassCurve R} {π : R} (hπ : π ≠ 0) {start n depth : ℕ}
  (data : (i : Fin (n + 1)) → Data W π (start + i.val))
  (D : SplitNodeDepth W π depth) (j : ℕ) (hj : j + 1 ≤ n)
  (hk0 : 0 < start + j) (hk : 2 * (start + j + 1) ≤ depth)
  (hjNext : j + 2 ≤ n)
  (r : ℕ) (hr : j + 2 + r ≤ n)
open WeierstrassSuccessiveX
local notation "K" => ResidueField R
local notation "e" => data (Fin.mk (j + 1) (Nat.lt_succ_of_le hj))
local notation "fData" => data (Fin.mk (j + 2) (Nat.lt_succ_of_le hjNext))
local notation "copen" => residueDividedConicOpenEquiv D (start + j) hk
  (Data.b3 e) (Data.b4 e) (Data.b6 e) (Data.factor3 e) (Data.factor4 e)
local notation "q" => Spec.map (CommRingCat.ofHom (AlgHom.toRingHom (AlgEquiv.toAlgHom copen)))
local notation "x" => WeierstrassDilatation.x W (π ^ (start + j + 1))
  (Data.b3 e) (Data.b4 e) (Data.b6 e)
local notation "t" => coord W (π ^ (start + j)) π (Data.b3 e) (Data.b4 e) (Data.b6 e) 0
local notation "uNext" => coord W (π ^ (start + (j + 1))) π
  (Data.b3 fData) (Data.b4 fData) (Data.b6 fData) 2
local notation "A" => PrincipalOpenTensor.transitionIso K x t
  (depthOverlapEquiv W π (start + j) (Data.b3 e) (Data.b4 e) (Data.b6 e))
local notation "B" => PrincipalOpenTensor.transitionIso K x uNext
  (previousBoundaryEquiv hπ e fData)
local notation "g" => adjacentRetainedOldGlobalTensorChart hπ data K j hj r hr
local notation "gNext" => olderGlobalTensorChart hπ data K (j + 1) hjNext r hr
local notation "E" => residueConicBoundaryIso D (start + j) hk0 hk
  (Data.b3 e) (Data.b4 e) (Data.b6 e) (Data.factor3 e) (Data.factor4 e)

/-- Normalize the entire adjacent intersection, preserving both original projections. -/
theorem adjacentRetainedNormalized_isPullback :
    IsPullback ((E).hom ≫ PrincipalOpenTensor.inclusion K t)
      (q ≫ (B).inv ≫ PrincipalOpenTensor.inclusion K uNext) g gNext := by
  let Q := Scheme.Spec.mapIso (copen).toRingEquiv.toCommRingCatIso.op
  apply (adjacentRetainedGlobalTensor_isPullback hπ data K j hj hjNext r hr).of_iso'
    Q (Iso.refl _) (Iso.refl _) (Iso.refl _)
  · change q ≫ (A).inv ≫ PrincipalOpenTensor.inclusion K t =
      ((E).hom ≫ PrincipalOpenTensor.inclusion K t) ≫ 𝟙 _
    simpa only [Category.comp_id] using
      residueDividedConicOpen_spec_boundary_assoc D (start + j) hk0 hk
        (Data.b3 e) (Data.b4 e) (Data.b6 e) (Data.factor3 e) (Data.factor4 e)
        (PrincipalOpenTensor.inclusion K t)
  · simp only [Iso.refl_hom, Category.comp_id]
    rfl
  · simp only [Iso.refl_hom, Category.comp_id, Category.id_comp]
  · simp only [Iso.refl_hom, Category.comp_id, Category.id_comp]

/-- The full original conic boundary identifies the actual adjacent fiber product. -/
def adjacentRetainedNormalizedPullbackIso :=
  (adjacentRetainedNormalized_isPullback hπ data D j hj hk0 hk hjNext r hr).isoPullback

/-- The first projection is the original conic boundary isomorphism and inclusion. -/
@[reassoc] theorem adjacentRetainedNormalizedPullbackIso_old :
    (adjacentRetainedNormalizedPullbackIso hπ data D j hj hk0 hk hjNext r hr).hom ≫
      pullback.fst g gNext = (E).hom ≫ PrincipalOpenTensor.inclusion K t :=
  (adjacentRetainedNormalized_isPullback hπ data D j hj hk0 hk hjNext r hr).isoPullback_hom_fst

/-- The second projection retains the actual inverse horizontal transition. -/
@[reassoc] theorem adjacentRetainedNormalizedPullbackIso_next :
    (adjacentRetainedNormalizedPullbackIso hπ data D j hj hk0 hk hjNext r hr).hom ≫
      pullback.snd g gNext = q ≫ (B).inv ≫ PrincipalOpenTensor.inclusion K uNext :=
  (adjacentRetainedNormalized_isPullback hπ data D j hj hk0 hk hjNext r hr).isoPullback_hom_snd

end FLT.Mazur.WeierstrassDividedDepth
