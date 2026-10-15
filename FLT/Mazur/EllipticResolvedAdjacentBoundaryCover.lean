/-
Copyright (c) 2026 krandder. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: krandder
-/
module

public import FLT.Mazur.EllipticAdjacentRetainedBoundaryCover
public import FLT.Mazur.EllipticFiniteTensorAtlasTransport
public import FLT.Mazur.EllipticResolvedExteriorBoundaryCover

/-!
# Adjacent boundaries in the original final resolved fiber

Reassociate the earlier conic map before transporting to the final stage.
Its whole image is the next retained arithmetic boundary.
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
  (hk0 : 0 < start + j) (hk : 2 * (start + j + 1) ≤ depth)
  (hjNext : j + 2 ≤ n) (r : ℕ) (hr : j + 2 + r ≤ n)
  (m : ℕ) (hm : m ≤ n) (he : j + 2 + r = m)
local notation "F" => ResidueField A
local notation "E₁" => finiteTensorIndexIso A hπ data F
  (j + 1 + (r + 1)) (j + 2 + r) (by omega) hr (by omega)
local notation "E₂" => finiteTensorIndexIso A hπ data F (j + 2 + r) m hr hm he
local notation "E₃" => finiteTensorIndexIso A hπ data F
  (j + 1 + (r + 1)) m (by omega) hm (by omega)

/-- Changing an equal retention count preserves the entire original map to a fixed stage. -/
theorem olderConicBoundary_final_retention_congr (s : ℕ)
    (hs : j + 1 + s ≤ n) (he' : j + 1 + s = m) (hrs : r + 1 = s) :
    olderGlobalConicBoundary hπ data D j hj (r + 1) (by omega) hk0 hk ≫ (E₃).hom =
    olderGlobalConicBoundary hπ data D j hj s hs hk0 hk ≫
      (finiteTensorIndexIso A hπ data F (j + 1 + s) m hs hm he').hom := by
  subst s
  rfl

/-- The conic range equality survives the original reassociation and final-stage transport. -/
theorem olderConicBoundary_final_range_eq_next :
    Set.range (olderGlobalConicBoundary hπ data D j hj (r + 1) (by omega) hk0 hk ≫
      (E₃).hom) =
    Set.range (finiteRetainedBoundaryTensorChart A hπ data (j + 1) hjNext r hr F ≫
      (E₂).hom) := by
  have hE : (E₁).hom ≫ (E₂).hom = (E₃).hom :=
    finiteTensorIndexIso_comp A hπ data F (by omega) hr hm (by omega) he
  rw [← hE, ← Category.assoc, finiteTensorIndexIso_eqToHom,
    olderConicBoundary_reassociate]
  simp only [Scheme.Hom.comp_base, TopCat.coe_comp, Set.range_comp]
  rw [adjacentRetainedConicBoundary_range_eq_retained A hπ data D j hj hk0 hk hjNext r hr]
end Transport

variable {W : WeierstrassCurve A} {π : A} {depth : ℕ} (D : SplitNodeDepth W π depth)
  (j : ℕ) (hj0 : 0 < j) (hj : j < depth / 2) (hjNext : j + 1 < depth / 2)

/-- The full conic boundary is exactly the next arithmetic boundary in the final fiber. -/
theorem resolvedRetainedConicChart_range_eq_next :
    Set.range (resolvedRetainedConicChart A D j hj0 hj) =
      Set.range (resolvedRetainedBoundaryChart A D (j + 1) hjNext) := by
  have h := olderConicBoundary_final_retention_congr A
    (SplitNodeDepth.uniformizer_ne_zero D) (splitResolutionData A D) D j (by omega)
    (by omega) (by omega) (r := depth / 2 - (j + 2)) (m := depth / 2)
    (hm := le_refl _) (he := by omega) (s := depth / 2 - (j + 1))
    (hs := by omega) (he' := by omega) (hrs := by omega)
  exact (congrArg (fun f : _ ⟶ _ => Set.range f) h.symm).trans
    (olderConicBoundary_final_range_eq_next A (SplitNodeDepth.uniformizer_ne_zero D)
      (splitResolutionData A D) D j (by omega) (by omega) (by omega) (by omega)
      (depth / 2 - (j + 2)) (by omega) (depth / 2) (le_refl _) (by omega))

include hj0 in
/-- Adjacent arithmetic boundaries give the exact smooth cover of an interior exterior. -/
theorem resolvedRetainedExterior_smooth_adjacent_cover :
    Set.range (resolvedRetainedBoundaryChart A D j hj) ∪
      Set.range (resolvedRetainedBoundaryChart A D (j + 1) hjNext) =
    Set.range (resolvedRetainedExteriorChart A D j hj) ∩
      (resolvedSplitStructure A D).smoothLocus.carrier := by
  rw [← resolvedRetainedConicChart_range_eq_next A D j hj0 hj hjNext]
  exact resolvedRetainedExterior_smooth_boundary_cover A D j hj0 hj

end FLT.Mazur.WeierstrassDividedDepth
