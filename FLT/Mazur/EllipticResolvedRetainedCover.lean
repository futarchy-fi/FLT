/-
Copyright (c) 2026 krandder. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: krandder
-/
module

public import FLT.Mazur.EllipticRetainedTrivializedCover
public import FLT.Mazur.EllipticResolvedRetainedSmoothCharts

/-!
# Retained geometric coverage in the original resolved fiber

Transport the full retained boundary open to the final index of the original
resolution. Its two arithmetic tori cover it exactly and are disjoint, both
in the resolved fiber and in its smooth locus.
-/

@[expose] public noncomputable section
open AlgebraicGeometry CategoryTheory IsLocalRing
open scoped TensorProduct
namespace FLT.Mazur.WeierstrassDividedDepth
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
universe u
variable {K : Type u} [Field K] (A : ValuationSubring K)
  {W : WeierstrassCurve A} {π : A} {depth : ℕ} (D : SplitNodeDepth W π depth)
  (r : (ResidueField A)ˣ) (j : ℕ) (hj0 : 0 < j) (hj : j < depth / 2)
local notation "F" => ResidueField A
local notation "data" => splitResolutionData A D
local notation "hπ" => SplitNodeDepth.uniformizer_ne_zero D
local notation "t" => depth / 2 - (j + 1)
local notation "E" => finiteTensorIndexIso A hπ data F
  (j + 1 + t) (depth / 2) (by omega) (le_refl _) (by omega)
local notation "d" => data (Fin.mk j (by omega))
local notation "B" => WeierstrassDilatation.HorizontalCoordinate W (π ^ (0 + j))
  (Data.b3 d) (Data.b4 d) (Data.b6 d)
local notation "pos" => resolvedRetainedPositiveChart A D r j hj0 hj
local notation "neg" => resolvedRetainedNegativeChart A D r j hj0 hj

/-- The full retained boundary open at the actual final index of the original model. -/
def resolvedRetainedBoundaryChart : Spec (.of (F ⊗[A] B)) ⟶ resolvedSplitFiber A D :=
  finiteRetainedBoundaryTensorChart A hπ data j (by omega) t (by omega) F ≫ (E).hom

instance resolvedRetainedBoundaryChart_isOpenImmersion :
    IsOpenImmersion (resolvedRetainedBoundaryChart A D j hj) :=
  inferInstanceAs (IsOpenImmersion (_ ≫ _))

/-- Both original arithmetic tori cover exactly the full retained boundary open. -/
theorem resolvedRetainedCharts_cover :
    Set.range neg ∪ Set.range pos = Set.range (resolvedRetainedBoundaryChart A D j hj) := by
  have h := retainedTrivializedCharts_cover A hπ data D r j
    (by omega) t (by omega) (by omega) (by omega)
  change Set.range (_ ≫ (E).hom) ∪ Set.range (_ ≫ (E).hom) = Set.range (_ ≫ (E).hom)
  simp only [Scheme.Hom.comp_base, TopCat.coe_comp, Set.range_comp]
  rw [← Set.image_union, h]

/-- Transport to the final index preserves disjointness of the two retained tori. -/
theorem resolvedRetainedCharts_disjoint : Disjoint (Set.range neg) (Set.range pos) := by
  apply Set.disjoint_left.mpr
  rintro z ⟨a, ha⟩ ⟨b, hb⟩
  have he := (E).hom.isOpenEmbedding.injective (ha.trans hb.symm)
  exact Set.disjoint_left.mp (retainedTrivializedCharts_disjoint A hπ data D r j
    (by omega) t (by omega) (by omega) (by omega)) ⟨a, rfl⟩ ⟨b, he.symm⟩

include r hj0 in
/-- The entire retained boundary open lies in the actual original smooth fiber. -/
theorem resolvedRetainedBoundaryChart_mem_smooth
    (z : Spec (.of (F ⊗[A] B))) :
    resolvedRetainedBoundaryChart A D j hj z ∈ (resolvedSplitStructure A D).smoothLocus := by
  have hz : resolvedRetainedBoundaryChart A D j hj z ∈
      Set.range neg ∪ Set.range pos := by
    rw [resolvedRetainedCharts_cover]
    exact ⟨z, rfl⟩
  rcases hz with ⟨a, ha⟩ | ⟨a, ha⟩
  · rw [← ha]
    exact resolvedRetainedNegativeChart_mem_smooth A D r j hj0 hj a
  · rw [← ha]
    exact resolvedRetainedPositiveChart_mem_smooth A D r j hj0 hj a

/-- The two retained components stay disjoint inside the original smooth locus. -/
theorem resolvedRetainedSmoothCharts_disjoint :
    Disjoint (Set.range (resolvedRetainedNegativeSmoothChart A D r j hj0 hj))
      (Set.range (resolvedRetainedPositiveSmoothChart A D r j hj0 hj)) := by
  apply Set.disjoint_left.mpr
  rintro z ⟨a, ha⟩ ⟨b, hb⟩
  have he := congrArg (fun x => (resolvedSplitStructure A D).smoothLocus.ι x)
    (ha.trans hb.symm)
  have hn := congrArg (fun f => f a)
    (resolvedRetainedNegativeSmoothChart_inclusion A D r j hj0 hj)
  have hp := congrArg (fun f => f b)
    (resolvedRetainedPositiveSmoothChart_inclusion A D r j hj0 hj)
  exact Set.disjoint_left.mp (resolvedRetainedCharts_disjoint A D r j hj0 hj)
    ⟨a, rfl⟩ ⟨b, (hn.symm.trans (he.trans hp)).symm⟩

end FLT.Mazur.WeierstrassDividedDepth
