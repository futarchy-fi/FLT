/-
Copyright (c) 2026 krandder. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: krandder
-/
module

public import FLT.Mazur.WeierstrassModificationXArithmeticNodeOverlap
public import FLT.Mazur.WeierstrassDividedArithmeticBoundaryCharts

/-!
# The two full initial nodes in every retained arithmetic stage

Their exact D(q) overlap and their joint coverage survive the original global
embedding. The other endpoint D(p) is not used for this intersection.
-/

@[expose] public noncomputable section
open AlgebraicGeometry CategoryTheory Limits
namespace FLT.Mazur.WeierstrassDividedDepth
open WeierstrassModificationX PolygonArithmeticStages
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
attribute [local irreducible] finiteGlobalModel finiteGlobalContraction
variable {R : Type} [CommRing R] [IsDomain R] [IsBezout R]
  {W : WeierstrassCurve R} {π : R} (hπ : π ≠ 0) {start n : ℕ}
  (data : (i : Fin (n + 1)) → Data W π (start + i.val)) (m : ℕ)
  (j : ℕ) (hj : j ≤ n)
local notation "Q" => Quotient R π m
local notation "d" => data (Fin.mk 0 (Nat.zero_lt_succ n))
variable (ha : IsUnit W.a₁) (h2 : π ∣ W.a₂)
  (h3 : π ∣ (data ⟨0, Nat.zero_lt_succ n⟩).b3)
  (h4 : π ∣ (data ⟨0, Nat.zero_lt_succ n⟩).b4)
  (h6 : π ∣ (data ⟨0, Nat.zero_lt_succ n⟩).b6)
local notation "F" => arithmeticInitialTensorNodeChart π m W (π ^ start)
  (Data.b3 d) (Data.b4 d) (Data.b6 d) ha h2 h3 h4 h6
local notation "G" => arithmeticOppositeInitialTensorNodeChart π m W (π ^ start)
  (Data.b3 d) (Data.b4 d) (Data.b6 d) ha h2 h3 h4 h6
local notation "i" => finiteArithmeticInitialTensorChart hπ data m j hj
local notation "P" => polynomialNodeOverlapInclusion
  (W.map (algebraMap R Q)) (algebraMap R Q (π ^ start))
local notation "B" => arithmeticNodeOverlapOpposite π m W (π ^ start)
  (Data.b3 d) (Data.b4 d) (Data.b6 d) ha h2 h3 h4 h6

/-- The complete standard D(q) is the full initial-node intersection after every retention. -/
theorem initialArithmeticNodes_isPullback : IsPullback P B (F ≫ i) (G ≫ i) := by
  let _ := finiteArithmeticInitialTensorChart_isOpenImmersion hπ data m j hj
  have H := arithmeticTensorNodes_isPullback π m W (π ^ start)
    (Data.b3 d) (Data.b4 d) (Data.b6 d) ha h2 h3 h4 h6
  exact IsPullback.of_isLimit (PullbackCone.isLimitOfCompMono _ _ i H.cone H.isLimit)

/-- The exact initial-node overlap retains both original global arithmetic maps. -/
@[reassoc] theorem initialArithmeticNodes_overlap : P ≫ F ≫ i = B ≫ G ≫ i := by
  simpa only [Category.assoc] using
    (initialArithmeticNodes_isPullback hπ data m j hj ha h2 h3 h4 h6).w

/-- Both constructed full nodes cover exactly the original retained initial tensor chart. -/
theorem initialArithmeticNodes_range_union :
    Set.range (F ≫ i) ∪ Set.range (G ≫ i) = Set.range i := by
  apply Set.Subset.antisymm
  · rintro _ (⟨x, rfl⟩ | ⟨x, rfl⟩)
    · exact ⟨F x, rfl⟩
    · exact ⟨G x, rfl⟩
  · rintro _ ⟨x, rfl⟩
    obtain ⟨y, hy⟩ | ⟨y, hy⟩ := arithmeticInitialTensorNodeCharts_cover π m W
      (π ^ start) (Data.b3 d) (Data.b4 d) (Data.b6 d) ha h2 h3 h4 h6 x
    · exact Or.inl ⟨y, congrArg i hy⟩
    · exact Or.inr ⟨y, congrArg i hy⟩

end FLT.Mazur.WeierstrassDividedDepth
