/-
Copyright (c) 2026 krandder. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: krandder
-/
module

public import FLT.Mazur.EllipticRetainedBoundaryAtlas
public import FLT.Mazur.EllipticResolvedRetainedCover
public import FLT.Mazur.WeierstrassDividedInfinitySmoothCompatibility

/-!
# The retained arithmetic components miss the original identity torus

The full retained boundary embeds in its positive-depth atlas member. The
atlas separation from infinity therefore proves geometric separation from
the entire original identity chart, without any hypothesis about point lifts.
-/

@[expose] public noncomputable section
open AlgebraicGeometry CategoryTheory IsLocalRing
namespace FLT.Mazur.WeierstrassDividedDepth
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
universe u
variable {K : Type u} [Field K] (A : ValuationSubring K)

section Index
variable {W : WeierstrassCurve A} {π : A} (hπ : π ≠ 0) {start n : ℕ}
  (data : (i : Fin (n + 1)) → Data W π (start + i.val))
  (S : Type u) [CommRing S] [Algebra A S]
  (i j : ℕ) (hi : i ≤ n) (hj : j ≤ n) (he : i = j)

/-- Equal stage transport preserves the actual full infinity tensor chart. -/
@[reassoc] theorem finiteTensorIndexIso_infinity :
    finiteInfinityTensorChart hπ data S i hi ≫
        (finiteTensorIndexIso A hπ data S i j hi hj he).hom =
      finiteInfinityTensorChart hπ data S j hj := by
  subst j
  exact Category.comp_id _
end Index

variable {W : WeierstrassCurve A} {π : A} {depth : ℕ} (D : SplitNodeDepth W π depth)
  (r : (ResidueField A)ˣ) (j : ℕ) (hj0 : 0 < j) (hj : j < depth / 2)
local notation "F" => ResidueField A
local notation "data" => splitResolutionData A D
local notation "hπ" => SplitNodeDepth.uniformizer_ne_zero D
local notation "t" => depth / 2 - (j + 1)
local notation "E" => finiteTensorIndexIso A hπ data F
  (j + 1 + t) (depth / 2) (by omega) (le_refl _) (by omega)
local notation "b" => resolvedRetainedBoundaryChart A D j hj
local notation "idc" => resolvedIdentityChart A D

include hj0 in
/-- The entire retained boundary is disjoint from the full original identity torus. -/
theorem resolvedRetainedBoundaryChart_identity_disjoint :
    Disjoint (Set.range b) (Set.range idc) := by
  rw [resolvedIdentityChart_range_infinity,
    ← finiteTensorIndexIso_infinity A hπ data F
      (j + 1 + t) (depth / 2) (by omega) (le_refl _) (by omega)]
  apply Set.disjoint_left.mpr
  rintro z ⟨a, ha⟩ ⟨x₂, hb⟩
  have he := (E).hom.isOpenEmbedding.injective (ha.trans hb.symm)
  exact Set.disjoint_left.mp (finiteRetainedBoundaryTensorChart_infinity_disjoint A
    hπ data j (by omega) t (by omega) D (by omega)) ⟨a, rfl⟩ ⟨x₂, he.symm⟩

/-- The positive retained arithmetic torus misses the complete original identity component chart. -/
theorem resolvedRetainedPositiveChart_identity_disjoint :
    Disjoint (Set.range (resolvedRetainedPositiveChart A D r j hj0 hj)) (Set.range idc) := by
  apply (resolvedRetainedBoundaryChart_identity_disjoint A D j hj0 hj).mono_left
  rw [← resolvedRetainedCharts_cover A D r j hj0 hj]
  exact Set.subset_union_right

/-- The negative retained arithmetic torus misses the complete original identity component chart. -/
theorem resolvedRetainedNegativeChart_identity_disjoint :
    Disjoint (Set.range (resolvedRetainedNegativeChart A D r j hj0 hj)) (Set.range idc) := by
  apply (resolvedRetainedBoundaryChart_identity_disjoint A D j hj0 hj).mono_left
  rw [← resolvedRetainedCharts_cover A D r j hj0 hj]
  exact Set.subset_union_left

end FLT.Mazur.WeierstrassDividedDepth
