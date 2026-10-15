/-
Copyright (c) 2026 krandder. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: krandder
-/
module

public import FLT.Mazur.EllipticResolvedRetainedCover
public import FLT.Mazur.EllipticZeroExteriorSmoothCover
public import FLT.Mazur.EllipticIncidenceBoundaryTransport
public import FLT.Mazur.EllipticResolvedExteriorBoundaryCover
public import FLT.Mazur.SchemeSmoothChartTransport

/-!
# The zero-depth exterior in the actual final resolved fiber

The original two boundary opens cover its smooth restriction. The horizontal
boundary lies in infinity, and the incidence boundary reaches the next retained
boundary or the terminal member.
-/

@[expose] public noncomputable section
open AlgebraicGeometry CategoryTheory IsLocalRing
namespace FLT.Mazur.WeierstrassDividedDepth
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
universe u
variable {K : Type u} [Field K] (A : ValuationSubring K)

section Transport
variable {W : WeierstrassCurve A} {π : A} (hπ : π ≠ 0) {start n depth : ℕ}
  (data : (i : Fin (n + 1)) → Data W π (start + i.val))
  (D : SplitNodeDepth W π depth) (j : ℕ) (hj : j + 1 ≤ n)
  (r : ℕ) (hr : j + 1 + r ≤ n) (hk0 : start + j = 0)
  (hk : 2 * (start + j + 1) ≤ depth) (m : ℕ) (hm : m ≤ n) (he : j + 1 + r = m)
local notation "F" => ResidueField A
local notation "e" => data (Fin.mk (j + 1) (by omega))
local notation "x" => WeierstrassSuccessiveX.coord W (π ^ (start + j)) π
  (Data.b3 e) (Data.b4 e) (Data.b6 e) 0
local notation "g" => olderGlobalTensorChart hπ data F j hj r hr
local notation "b" => finiteRetainedBoundaryTensorChart A hπ data j hj r hr F
local notation "c" => PrincipalOpenTensor.inclusion F x ≫ g
local notation "E" => finiteTensorIndexIso A hπ data F (j + 1 + r) m hr hm he
local notation "p" => Limits.pullback.fst
  (Spec.map (CommRingCat.ofHom (algebraMap A F))) (finiteGlobalStructure hπ data m hm)

include D hk0 hk in
/-- The zero-exterior smooth cover transports before specializing recursive resolution data. -/
theorem zeroExterior_final_smooth_boundary_cover :
    Set.range (b ≫ (E).hom) ∪ Set.range (c ≫ (E).hom) =
      Set.range (g ≫ (E).hom) ∩ (p).smoothLocus.carrier := by
  subst m
  simpa only [finiteTensorIndexIso, Iso.refl_hom, Category.comp_id] using
    zeroExterior_smooth_boundary_cover A hπ data D j hj r hr hk0 hk
end Transport

variable {W : WeierstrassCurve A} {π : A} {depth : ℕ} (D : SplitNodeDepth W π depth)
  (j : ℕ) (hj : j < depth / 2)
local notation "F" => ResidueField A
local notation "data" => splitResolutionData A D
local notation "hπ" => SplitNodeDepth.uniformizer_ne_zero D
local notation "t" => depth / 2 - (j + 1)
local notation "E" => finiteTensorIndexIso A hπ data F
  (j + 1 + t) (depth / 2) (by omega) (le_refl _) (by omega)
local notation "g" => olderGlobalTensorChart hπ data F j (by omega) t (by omega)
local notation "b" => finiteRetainedBoundaryTensorChart A hπ data j
  (by omega) t (by omega) F
local notation "e" => data (Fin.mk (j + 1) (by omega))
local notation "x" => WeierstrassSuccessiveX.coord W (π ^ (0 + j)) π
  (Data.b3 e) (Data.b4 e) (Data.b6 e) 0
local notation "c" => PrincipalOpenTensor.inclusion F x ≫ g
local notation "p" => resolvedSplitStructure A D

/-- The original incidence open at the final resolved stage, including zero depth. -/
def resolvedRetainedIncidenceChart := c ≫ (E).hom

/-- The zero exterior has exactly the two original boundary opens as its smooth part. -/
theorem resolvedZeroExterior_smooth_boundary_cover (hj0 : j = 0) :
    Set.range (resolvedRetainedBoundaryChart A D j hj) ∪
      Set.range (resolvedRetainedIncidenceChart A D j hj) =
    Set.range (resolvedRetainedExteriorChart A D j hj) ∩ (p).smoothLocus.carrier := by
  exact zeroExterior_final_smooth_boundary_cover A hπ data D j (by omega)
    t (by omega) (by omega) (by omega) (depth / 2) (le_refl _) (by omega)

/-- The incidence open is exactly the next retained boundary when another stage remains. -/
theorem resolvedRetainedIncidenceChart_range_eq_next (hjNext : j + 1 < depth / 2) :
    Set.range (resolvedRetainedIncidenceChart A D j hj) =
      Set.range (resolvedRetainedBoundaryChart A D (j + 1) hjNext) := by
  have h := olderIncidenceBoundary_final_retention_congr A hπ data j (by omega)
    (r := depth / 2 - (j + 2)) (depth / 2) (depth / 2 - (j + 1)) (le_refl _)
    (by omega) (by omega) (by omega) (by omega) (by omega)
  exact (congrArg (fun f : _ ⟶ _ => Set.range f) h.symm).trans
    (olderIncidenceBoundary_final_range_eq_next A hπ data j (by omega) (by omega)
      (depth / 2 - (j + 2)) (by omega) (depth / 2) (le_refl _) (by omega))

/-- At the last stage the whole incidence boundary enters the actual terminal chart. -/
theorem resolvedLastIncidenceChart_range_subset_terminal (hlast : j + 1 = depth / 2) :
    Set.range (resolvedRetainedIncidenceChart A D j hj) ⊆
      Set.range (globalDividedTensorChart hπ data F (depth / 2) (le_refl _)) := by
  exact lastIncidenceBoundary_final_range_subset A hπ data j (by omega)
    (depth / 2 - (j + 1)) (depth / 2) (by omega) (le_refl _) (by omega) hlast

end FLT.Mazur.WeierstrassDividedDepth
