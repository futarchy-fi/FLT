/-
Copyright (c) 2026 krandder. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: krandder
-/
module

public import FLT.Mazur.EllipticResolvedRetainedCover
public import FLT.Mazur.EllipticZeroExteriorSmoothCover

/-!
# The first retained boundary lies in the original identity chart

The full punctured slope image survives final-stage transport into infinity.
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

/-- Equal-stage transport preserves the complete original infinity chart. -/
theorem finiteTensorIndexIso_infinity_range :
    Set.range (finiteInfinityTensorChart hπ data F (j + 1 + r) hr ≫
      (finiteTensorIndexIso A hπ data F (j + 1 + r) m hr hm he).hom) =
    Set.range (finiteInfinityTensorChart hπ data F m hm) := by
  subst m
  rw [show (finiteTensorIndexIso A hπ data F (j + 1 + r) (j + 1 + r)
    hr hm rfl).hom = 𝟙 _ from rfl, Category.comp_id]

include D hk0 hk in
/-- The entire first arithmetic boundary enters infinity after final-stage transport. -/
theorem zeroRetainedBoundary_final_range_subset_infinity :
    Set.range (finiteRetainedBoundaryTensorChart A hπ data j hj r hr F ≫
      (finiteTensorIndexIso A hπ data F (j + 1 + r) m hr hm he).hom) ⊆
    Set.range (finiteInfinityTensorChart hπ data F m hm) := by
  rw [← finiteTensorIndexIso_infinity_range A hπ data j r hr m hm he]
  simp only [Scheme.Hom.comp_base, TopCat.coe_comp, Set.range_comp]
  exact Set.image_mono (zeroRetainedBoundary_range_subset_infinity
    A hπ data D j hj r hr hk0 hk)
end Transport

variable {W : WeierstrassCurve A} {π : A} {depth : ℕ} (D : SplitNodeDepth W π depth)
  (j : ℕ) (hj : j < depth / 2) (hj0 : j = 0)
local notation "F" => ResidueField A
local notation "data" => splitResolutionData A D
local notation "hπ" => SplitNodeDepth.uniformizer_ne_zero D

include hj0 in
/-- The zero-depth boundary is contained in the actual final infinity chart. -/
theorem resolvedZeroBoundary_range_subset_infinity :
    Set.range (resolvedRetainedBoundaryChart A D j hj) ⊆
      Set.range (finiteInfinityTensorChart hπ data F (depth / 2) (le_refl _)) := by
  exact zeroRetainedBoundary_final_range_subset_infinity A hπ data D j (by omega)
    (depth / 2 - (j + 1)) (by omega) (by omega) (by omega)
    (depth / 2) (le_refl _) (by omega)

end FLT.Mazur.WeierstrassDividedDepth
