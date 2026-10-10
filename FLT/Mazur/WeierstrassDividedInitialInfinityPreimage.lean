/-
Copyright (c) 2026 krandder. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: krandder
-/
module

public import FLT.Mazur.WeierstrassDividedInitialTensorChart
public import FLT.Mazur.WeierstrassDividedOlderInfinityPreimage

/-!
# The original initial chart meets infinity along its exact y principal open

The affine contraction persists through all finite retentions. Its original
y function therefore computes the whole infinity intersection, including
at start zero and with arbitrary original divided coefficients.
-/

@[expose] public noncomputable section
open AlgebraicGeometry CategoryTheory Limits
namespace FLT.Mazur.WeierstrassDividedDepth
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
variable {R : Type*} [CommRing R] [IsDomain R] [IsBezout R]
  {W : WeierstrassCurve R} {π : R} (hπ : π ≠ 0) {start n : ℕ}
  (data : (i : Fin (n + 1)) → Data W π (start + i.val))
  (j : ℕ) (hj : j ≤ n)
local notation "d" => data (Fin.mk 0 (Nat.zero_lt_succ n))
local notation "c" => finiteInitialChart hπ data j hj
local notation "y" => WeierstrassModificationX.y W (π ^ start)
  (Data.b3 d) (Data.b4 d) (Data.b6 d)
local notation "f" => Spec.map (CommRingCat.ofHom (AlgHom.toRingHom
  (WeierstrassModificationX.fromOriginal W (π ^ start)
    (Data.b3 d) (Data.b4 d) (Data.b6 d)
    (Data.factor3 d) (Data.factor4 d) (Data.factor6 d))))
open WeierstrassIntegralChart

omit [IsBezout R] in
/-- The original initial affine contraction is unchanged by every later retention. -/
@[reassoc] theorem finiteInitialChart_toAffine :
    c ≫ finiteToAffine hπ data j hj = f := by
  rw [← cancel_mono (integralCurveChart W 2), Category.assoc,
    finiteToAffine_toCurve, finiteInitialChart_toCurve]
  rfl

/-- Infinity cuts out precisely the original affine Y-boundary in the initial chart. -/
theorem finiteInitialChart_infinity_preimage :
    (c ≫ finiteLocalChart hπ data j hj) ⁻¹'
      Set.range (finiteInfinityChart hπ data j hj) =
        f ⁻¹' Set.range (overlapInclusion W 2 1) := by
  apply chart_preimage_of_contraction c (finiteLocalChart hπ data j hj)
    (finiteToAffine hπ data j hj) f _ _
  · rw [finiteYBoundary_preimage]
    exact SchemeOpenPushout.inr_preimage_inl _ _
  · exact finiteInitialChart_toAffine hπ data j hj

/-- The full initial/infinity intersection is the principal open of the original y function. -/
theorem finiteInitialChart_infinity_principal :
    (c ≫ finiteLocalChart hπ data j hj) ⁻¹'
      Set.range (finiteInfinityChart hπ data j hj) =
        Set.range (Spec.map (CommRingCat.ofHom (algebraMap _ (Localization.Away y)))) := by
  rw [finiteInitialChart_infinity_preimage]
  have H : Set.range (overlapInclusion W 2 1) =
      (PrimeSpectrum.basicOpen (coord W 2 1) : Set (PrimeSpectrum (Coordinate W 2))) :=
    PrincipalAffineRefinement.range_inclusion _
  rw [H]
  change (PrimeSpectrum.comap _) ⁻¹' _ =
    Set.range (PrimeSpectrum.comap (algebraMap _ (Localization.Away y)))
  rw [PrimeSpectrum.localization_away_comap_range _ y]
  change (↑(PrimeSpectrum.basicOpen
    (WeierstrassModificationX.fromOriginal W (π ^ start)
      (Data.b3 d) (Data.b4 d) (Data.b6 d)
      (Data.factor3 d) (Data.factor4 d) (Data.factor6 d) (coord W 2 1))) :
      Set (PrimeSpectrum (WeierstrassModificationX.Coordinate W (π ^ start)
        (Data.b3 d) (Data.b4 d) (Data.b6 d)))) = _
  rw [WeierstrassModificationX.fromOriginal_y]

end FLT.Mazur.WeierstrassDividedDepth
