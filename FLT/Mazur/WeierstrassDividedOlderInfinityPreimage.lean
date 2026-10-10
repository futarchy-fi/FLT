/-
Copyright (c) 2026 krandder. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: krandder
-/
module

public import FLT.Mazur.WeierstrassDividedSuccessiveOriginalY
public import FLT.Mazur.WeierstrassDividedOlderSuccessiveCharts
public import FLT.Mazur.WeierstrassDividedGlobalTensorGluing

/-!
# The exact infinity attachment on every retained successive chart

Infinity meets an older chart exactly where the original affine y coordinate
is invertible. The affine contraction and its full preimage survive all
later stages, before any fiber decomposition.
-/

@[expose] public noncomputable section
open AlgebraicGeometry CategoryTheory Limits
namespace FLT.Mazur.WeierstrassDividedDepth
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
/-- Composition of chart maps retains ordinary set preimages. -/
theorem chart_comp_preimage {X Y Z : Scheme} (f : X ⟶ Y) (g : Y ⟶ Z) (U : Set Z) :
    (f ≫ g) ⁻¹' U = f ⁻¹' (g ⁻¹' U) := rfl

/-- A retained contraction computes a chart's full preimage through an ambient open. -/
theorem chart_preimage_of_contraction {A B X Y : Scheme}
    (c : A ⟶ B) (l : B ⟶ X) (f : B ⟶ Y) (g : A ⟶ Y) (U : Set X) (V : Set Y)
    (hl : l ⁻¹' U = f ⁻¹' V) (hc : c ≫ f = g) : (c ≫ l) ⁻¹' U = g ⁻¹' V := by
  rw [chart_comp_preimage, hl, ← chart_comp_preimage, hc]

variable {R : Type*} [CommRing R] [IsDomain R] [IsBezout R]
  {W : WeierstrassCurve R} {π : R} (hπ : π ≠ 0) {start n : ℕ}
  (data : (i : Fin (n + 1)) → Data W π (start + i.val))
  (j : ℕ) (hj : j + 1 ≤ n) (r : ℕ) (hr : j + 1 + r ≤ n)
local notation "d" => data (Fin.mk j (Nat.lt_succ_of_le (Nat.le_of_succ_le hj)))
local notation "e" => data (Fin.mk (j + 1) (Nat.lt_succ_of_le hj))
local notation "c" => olderSuccessiveChart hπ data j hj r hr
open WeierstrassIntegralChart

omit [IsBezout R] in
/-- The complete original affine contraction of the retained successive chart. -/
@[reassoc] theorem olderSuccessiveChart_toAffine :
    c ≫ finiteToAffine hπ data (j + 1 + r) hr = xContraction hπ d e ≫ toAffine d := by
  rw [← cancel_mono (integralCurveChart W 2), Category.assoc, Category.assoc,
    finiteToAffine_toCurve, toAffine_toCurve, olderSuccessiveChart_toCurve]

/-- The full infinity preimage in the original local finite model is its Y-boundary. -/
theorem finiteLocalChart_infinity_preimage :
    finiteLocalChart hπ data (j + 1 + r) hr ⁻¹'
      Set.range (finiteInfinityChart hπ data (j + 1 + r) hr) =
        (finiteToAffine hπ data (j + 1 + r) hr) ⁻¹'
          Set.range (overlapInclusion W 2 1) := by
  rw [finiteYBoundary_preimage]
  exact SchemeOpenPushout.inr_preimage_inl _ _

/-- Every retained successive chart meets infinity in precisely the original affine Y-open. -/
theorem olderSuccessiveChart_infinity_preimage :
    (c ≫ finiteLocalChart hπ data (j + 1 + r) hr) ⁻¹'
      Set.range (finiteInfinityChart hπ data (j + 1 + r) hr) =
        (xContraction hπ d e ≫ toAffine d) ⁻¹' Set.range (overlapInclusion W 2 1) := by
  exact chart_preimage_of_contraction (B := finiteModification hπ data (j + 1 + r) hr)
    c (finiteLocalChart hπ data (j + 1 + r) hr) _ _ _ _
    (finiteLocalChart_infinity_preimage hπ data j r hr)
    (olderSuccessiveChart_toAffine hπ data j hj r hr)

/-- The infinity intersection is the entire principal open of the contracted original y. -/
theorem olderSuccessiveChart_infinity_basicOpen :
    (c ≫ finiteLocalChart hπ data (j + 1 + r) hr) ⁻¹'
      Set.range (finiteInfinityChart hπ data (j + 1 + r) hr) =
        (xContraction hπ d e ≫ toAffine d) ⁻¹'
          (PrimeSpectrum.basicOpen (coord W 2 1) : Set (PrimeSpectrum (Coordinate W 2))) := by
  have h : Set.range (overlapInclusion W 2 1) =
      (PrimeSpectrum.basicOpen (coord W 2 1) : Set (PrimeSpectrum (Coordinate W 2))) :=
    PrincipalAffineRefinement.range_inclusion _
  exact (olderSuccessiveChart_infinity_preimage hπ data j hj r hr).trans
    (congrArg (fun s => (xContraction hπ d e ≫ toAffine d) ⁻¹' s) h)

/-- Infinity has exactly the full scaled original y localization as its retained preimage. -/
theorem olderSuccessiveChart_infinity_principal :
    (c ≫ finiteLocalChart hπ data (j + 1 + r) hr) ⁻¹'
      Set.range (finiteInfinityChart hπ data (j + 1 + r) hr) =
        Set.range (Spec.map (CommRingCat.ofHom
          (algebraMap _ (Localization.Away (successiveOriginalY e))))) := by
  exact (olderSuccessiveChart_infinity_basicOpen hπ data j hj r hr).trans
    ((xContraction_originalY_preimage hπ d e).trans
      (PrimeSpectrum.localization_away_comap_range _ (successiveOriginalY e)).symm)

end FLT.Mazur.WeierstrassDividedDepth
