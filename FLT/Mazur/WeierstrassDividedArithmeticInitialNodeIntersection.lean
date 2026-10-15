/-
Copyright (c) 2026 krandder. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: krandder
-/
module

public import FLT.Mazur.WeierstrassDividedArithmeticInitialNodes
public import FLT.Mazur.WeierstrassDividedArithmeticInitialBranch
public import FLT.Mazur.WeierstrassModificationXArithmeticPuncture

/-!
# Exact intersections of full initial nodes with the first arithmetic branches

Each original labeled full node meets its first same-label polygon branch in
exactly the complete standard D(p), with the corrected original Laurent parameter.
-/

@[expose] public noncomputable section
open AlgebraicGeometry CategoryTheory Limits
namespace FLT.Mazur.WeierstrassDividedDepth
open WeierstrassSuccessiveX WeierstrassModificationX PolygonArithmeticStages
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
attribute [local irreducible] finiteGlobalModel finiteGlobalContraction
variable {R : Type} [CommRing R] [IsDomain R] [IsBezout R]
  {W : WeierstrassCurve R} {π : R} (hπ : π ≠ 0) {start n : ℕ}
  (data : (i : Fin (n + 1)) → Data W π (start + i.val)) (m : ℕ)
  (h1 : 1 ≤ n) (r : ℕ) (hr : 1 + r ≤ n)
local notation "Q" => Quotient R π m
local notation "d" => data (Fin.mk 0 (Nat.zero_lt_succ n))
local notation "e" => data (Fin.mk 1 (Nat.lt_succ_of_le h1))
variable (ha : IsUnit W.a₁) (hs : π ∣ π ^ start) (h2 : π ∣ W.a₂)
  (hd3 : π ∣ (data ⟨0, Nat.zero_lt_succ n⟩).b3)
  (hd4 : π ∣ (data ⟨0, Nat.zero_lt_succ n⟩).b4)
  (hd6 : π ∣ (data ⟨0, Nat.zero_lt_succ n⟩).b6)
  (he3 : π ∣ (data ⟨1, Nat.lt_succ_of_le h1⟩).b3)
  (he4 : π ∣ (data ⟨1, Nat.lt_succ_of_le h1⟩).b4)
  (he6 : π ∣ (data ⟨1, Nat.lt_succ_of_le h1⟩).b6) (opposite : Bool)
local notation "c" => arithmeticTensorBranchChart π m W (π ^ start)
  (Data.b3 e) (Data.b4 e) (Data.b6 e) ha hs h2 he3 he4 he6 opposite
local notation "i" => finiteArithmeticInitialTensorChart hπ data m (1 + r) hr
local notation "a" => finiteArithmeticOlderTensorChart hπ data m 0 h1 r hr
local notation "G" => arithmeticInitialNodeRestriction π m W (π ^ start)
  (Data.b3 d) (Data.b4 d) (Data.b6 d) ha h2 hd3 hd4 hd6 hs
local notation "B" => initialArithmeticBranchBoundary hπ data m h1 ha hs h2 he3 he4 he6 opposite
local notation "N" => ite (opposite = true)
  (arithmeticOppositeInitialTensorNodeChart π m W (π ^ start)
    (Data.b3 d) (Data.b4 d) (Data.b6 d) ha h2 hd3 hd4 hd6)
  (arithmeticInitialTensorNodeChart π m W (π ^ start)
    (Data.b3 d) (Data.b4 d) (Data.b6 d) ha h2 hd3 hd4 hd6)

omit [IsBezout R] in
/-- The original labeled initial boundary factors through its constructed full node chart. -/
@[reassoc] theorem initialArithmeticNode_boundary : G ≫ N = B := by
  cases opposite
  · exact arithmeticInitialFullNode_boundary hπ d e m ha hs h2 hd3 hd4 hd6 he3 he4 he6
  · exact arithmeticOppositeInitialFullNode_boundary hπ d e m ha hs h2 hd3 hd4 hd6 he3 he4 he6

/-- The original full initial node and the first same-label branch have the full Laurent overlap. -/
theorem initialArithmeticNode_isPullback :
    IsPullback G (PolygonSmoothing.rightBranchOpen Q (parameter R π m))
      (N ≫ i) (c ≫ a) := by
  have hn : IsOpenImmersion N := by
    cases opposite
    · exact arithmeticInitialTensorNodeChart_isOpenImmersion
        π m W (π ^ start) (Data.b3 d) (Data.b4 d) (Data.b6 d) ha h2 hd3 hd4 hd6
    · exact arithmeticOppositeInitialTensorNodeChart_isOpenImmersion
        π m W (π ^ start) (Data.b3 d) (Data.b4 d) (Data.b6 d) ha h2 hd3 hd4 hd6
  have H := initialArithmeticBranch_isPullback hπ data m h1 r hr ha hs h2 he3 he4 he6 opposite
  rw [← initialArithmeticNode_boundary hπ data m h1 ha hs h2
    hd3 hd4 hd6 he3 he4 he6 opposite] at H
  have H' : IsPullback (𝟙 (PolygonSmoothing.branchTorus Q)) G (G ≫ N) N :=
    IsPullback.of_horiz_isIso_mono ⟨by simp only [Category.id_comp]⟩
  simpa only [Category.id_comp] using (H'.paste_horiz H.flip).flip

local notation "P" => arithmeticInitialPunctureInclusion π m W (π ^ start) ha hs
local notation "E" => arithmeticInitialPunctureIso π m W (π ^ start)
  (Data.b3 d) (Data.b4 d) (Data.b6 d) ha hs h2 hd3 hd4 hd6

/-- The complete standard D(p) is exactly the full-node/first-branch intersection. -/
theorem initialArithmeticStandardPuncture_isPullback :
    IsPullback P ((E).inv ≫ PolygonSmoothing.rightBranchOpen Q (parameter R π m))
      (N ≫ i) (c ≫ a) := by
  apply (initialArithmeticNode_isPullback hπ data m h1 r hr ha hs h2
    hd3 hd4 hd6 he3 he4 he6 opposite).of_iso E (Iso.refl _) (Iso.refl _) (Iso.refl _)
  · simpa only [Iso.refl_hom, Category.comp_id] using
      (arithmeticInitialPunctureIso_boundary π m W (π ^ start)
        (Data.b3 d) (Data.b4 d) (Data.b6 d) ha hs h2 hd3 hd4 hd6).symm
  · simp
  · simp
  · simp

/-- The corrected initial puncture maps agree in the actual retained global arithmetic stage. -/
@[reassoc] theorem initialArithmeticStandardPuncture_overlap :
    P ≫ N ≫ i = (E).inv ≫ PolygonSmoothing.rightBranchOpen Q (parameter R π m) ≫ c ≫ a :=
  (initialArithmeticStandardPuncture_isPullback hπ data m h1 r hr ha hs h2
    hd3 hd4 hd6 he3 he4 he6 opposite).w

end FLT.Mazur.WeierstrassDividedDepth
