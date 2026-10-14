/-
Copyright (c) 2026 krandder. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: krandder
-/
module

public import FLT.Mazur.EllipticFiniteRetainedLaurentCharts

/-!
# Both Laurent charts cover the original retained open

The chart reconstruction does not discard any geometric points of the retained
horizontal tensor open. The two oriented Laurent images are disjoint there.
-/

@[expose] public noncomputable section
open AlgebraicGeometry CategoryTheory IsLocalRing
namespace FLT.Mazur.WeierstrassDividedDepth
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
universe u
variable {K : Type u} [Field K] (A : ValuationSubring K)
  {W : WeierstrassCurve A} {π : A} (hπ : π ≠ 0) {start n depth : ℕ}
  (data : (i : Fin (n + 1)) → Data W π (start + i.val))
  (D : SplitNodeDepth W π depth) (j : ℕ) (hj : j + 1 ≤ n)
  (r : ℕ) (hr : j + 1 + r ≤ n)
  (hk0 : 0 < start + j) (hp : 2 * (start + j) < depth)
local notation "F" => ResidueField A
local notation "d" => data (Fin.mk j (Nat.lt_succ_of_le (Nat.le_of_succ_le hj)))
local notation "c" => finiteRetainedBoundaryTensorChart A hπ data j hj r hr F
local notation "l" => retainedNegativeLaurentChart A hπ data D j hj r hr hk0 hp
local notation "q" => retainedPositiveLaurentChart A hπ data D j hj r hr hk0 hp
local notation "E" => WeierstrassDilatation.residueHorizontalDifferenceIso D (start + j)
  hk0 (by omega) (Data.b3 d) (Data.b4 d) (Data.b6 d)
  (Data.factor3 d) (Data.factor4 d) (Data.factor6 d) hp
local notation "a" => (WeierstrassDilatation.residueTangentUnit D)⁻¹

/-- Both oriented Laurent charts cover exactly the entire original retained tensor open. -/
theorem retainedLaurentCharts_cover : Set.range l ∪ Set.range q = Set.range c := by
  apply Set.Subset.antisymm
  · rintro z (⟨t, rfl⟩ | ⟨t, rfl⟩)
    · exact ⟨_, rfl⟩
    · exact ⟨_, rfl⟩
  · rintro z ⟨t, rfl⟩
    have ht := WeierstrassDilatation.residueHorizontalBranches_cover D (start + j)
      hk0 (by omega) (Data.b3 d) (Data.b4 d) (Data.b6 d)
      (Data.factor3 d) (Data.factor4 d) (Data.factor6 d) hp t
    rcases ht with ⟨u, hu⟩ | ⟨u, hu⟩
    · exact Or.inl ⟨u, congrArg (fun z => c z) hu⟩
    · exact Or.inr ⟨u, congrArg (fun z => c z) hu⟩

/-- Retention does not identify the two original oriented punctures. -/
theorem retainedLaurentCharts_disjoint : Disjoint (Set.range l) (Set.range q) := by
  apply Set.disjoint_left.mpr
  rintro z ⟨u, hu⟩ ⟨v, hv⟩
  have he := (c).isOpenEmbedding.injective (hu.trans hv.symm)
  have he := (E).hom.isOpenEmbedding.injective he
  have he := congrArg (fun z => PolygonNodeDifferenceBranches.inclusion a z) he
  have hl := congrArg (fun f => f u) (PolygonNodeDifferenceBranches.left_inclusion a)
  have hr := congrArg (fun f => f v) (PolygonNodeDifferenceBranches.right_inclusion a)
  have he : PolygonNodeBranches.left F u = PolygonNodeBranches.right F v :=
    hl.symm.trans (he.trans hr)
  exact Set.disjoint_left.mp (PolygonNodeBranches.disjoint_ranges F)
    ⟨u, rfl⟩ ⟨v, he.symm⟩

end FLT.Mazur.WeierstrassDividedDepth
