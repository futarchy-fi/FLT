/-
Copyright (c) 2026 krandder. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: krandder
-/
module

public import FLT.Mazur.WeierstrassDividedArithmeticLabeledInitialEdge
public import FLT.Mazur.WeierstrassDividedArithmeticLabeledAdjacent
public import FLT.Mazur.WeierstrassDividedArithmeticLabeledTerminalEdge

/-!
# Explicit edge equations for the full positive-retention labeled atlas

The first, consecutive and terminal equations use the original standard
punctures and their full parameter changes, at both Boolean labels.
-/

@[expose] public noncomputable section
open AlgebraicGeometry CategoryTheory Limits
namespace FLT.Mazur.WeierstrassDividedDepth
open PolygonArithmeticStages WeierstrassModificationX
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
attribute [local irreducible] finiteGlobalModel finiteGlobalContraction
variable {R : Type} [CommRing R] [IsDomain R] [IsBezout R]
  {W : WeierstrassCurve R} {π : R} (hπ : π ≠ 0) {start n : ℕ}
  (data : (i : Fin (n + 1)) → Data W π (start + i.val))
  (H : ArithmeticAtlasCoefficients data) (m j : ℕ) (hj : j + 1 ≤ n)
local notation "Q" => Quotient R π m
local notation "d₀" => data (Fin.mk 0 (Nat.zero_lt_succ n))
local notation "d₁" => data (Fin.mk (j + 1) (Nat.lt_succ_of_le hj))
local notation "c" => arithmeticLabeledAtlasMap hπ data H m (j + 1) hj
local notation "P" => arithmeticInitialPunctureInclusion π m W (π ^ start) H.a1_unit H.scale_div
local notation "E" => arithmeticInitialPunctureIso π m W (π ^ start)
  (Data.b3 d₀) (Data.b4 d₀) (Data.b6 d₀) H.a1_unit H.scale_div H.a2_div
    (H.b3_div _) (H.b4_div _) (H.b6_div _)
local notation "s" => WeierstrassDilatation.arithmeticTerminalSmoothing π m W
  (π ^ (start + (j + 1))) (Data.b3 d₁) (Data.b4 d₁) (Data.b6 d₁)
    H.a1_unit (H.scale (j + 1)) H.a2_div (H.b4_div _) (H.b6_div _)
variable {Y : Scheme.{0}}
  (f : ∀ i, arithmeticLabeledAtlasObject hπ data H m (j + 1) hj i ⟶ Y)
local notation "C" => fun (i k : ArithmeticChartLabel (j + 1)) =>
  pullback.fst (c i) (c k) ≫ f i = pullback.snd (c i) (c k) ≫ f k

/-- The two full initial D(p) equations retain their original inverse Laurent parameter. -/
def arithmeticPositiveInitialCompatible : Prop :=
  ∀ b : Bool, P ≫ f (.initial b) =
    ((E).inv ≫ PolygonSmoothing.rightBranchOpen Q (parameter R π m)) ≫
      f (.retained ⟨0, Nat.zero_lt_succ j⟩ b)

/-- Every consecutive same-label edge uses the original left/preceding polygon maps. -/
def arithmeticPositiveAdjacentCompatible : Prop :=
  ∀ (a : ℕ) (ha : a + 1 < j + 1) (b : Bool),
    PolygonSmoothing.leftBranchOpen Q (parameter R π m) ≫ f (.retained ⟨a, by omega⟩ b) =
      PolygonSmoothing.precedingBranch Q (parameter R π m) ≫ f (.retained ⟨a + 1, ha⟩ b)

/-- Both terminal standard punctures retain the full original Laurent comparison. -/
def arithmeticPositiveTerminalCompatible : Prop :=
  ∀ b : Bool,
    Spec.map (CommRingCat.ofHom (algebraMap (NodalFiber.Coordinate s)
      (Localization.Away (ite (b = true) (NodalFiber.p s) (NodalFiber.q s))))) ≫
        f .terminal =
    ((terminalArithmeticPunctureIso data m j hj H.a1_unit
      (H.scale j) H.a2_div (H.b3_div _) (H.b4_div _) (H.b6_div _) b).inv ≫
        PolygonSmoothing.leftBranchOpen Q (parameter R π m)) ≫ f (.retained ⟨j, by omega⟩ b)

/-- The first two explicit equations characterize the entire initial/first-label fiber products. -/
theorem arithmeticPositiveInitial_compatible_iff :
    arithmeticPositiveInitialCompatible hπ data H m j hj f ↔
      ∀ b : Bool, C (.initial b) (.retained ⟨0, Nat.zero_lt_succ j⟩ b) := by
  unfold arithmeticPositiveInitialCompatible
  apply forall_congr'
  intro b
  dsimp only
  have T := arithmeticLabeledAtlas_initial_edge_isPullback
    hπ data H m (j + 1) hj (Nat.zero_lt_succ j) b
  rw [← cancel_epi T.isoPullback.hom]
  simp only [← Category.assoc, IsPullback.isoPullback_hom_fst,
    IsPullback.isoPullback_hom_snd]

/-- Consecutive full labeled fiber products impose exactly the original polygon edge equations. -/
theorem arithmeticPositiveAdjacent_compatible_iff :
    arithmeticPositiveAdjacentCompatible hπ data H m j hj f ↔
      ∀ (a : ℕ) (ha : a + 1 < j + 1) (b : Bool),
        C (.retained ⟨a, by omega⟩ b) (.retained ⟨a + 1, ha⟩ b) := by
  unfold arithmeticPositiveAdjacentCompatible
  apply forall_congr'
  intro a
  apply forall_congr'
  intro ha
  apply forall_congr'
  intro b
  dsimp only
  have T := arithmeticLabeledAtlas_adjacent_isPullback hπ data H m (j + 1) hj a ha b
  rw [← cancel_epi T.isoPullback.hom]
  simp only [← Category.assoc, IsPullback.isoPullback_hom_fst,
    IsPullback.isoPullback_hom_snd]

/-- The two full terminal fiber-product tests are precisely the standard puncture equations. -/
theorem arithmeticPositiveTerminal_compatible_iff :
    arithmeticPositiveTerminalCompatible hπ data H m j hj f ↔
      ∀ b : Bool, C .terminal (.retained ⟨j, by omega⟩ b) := by
  unfold arithmeticPositiveTerminalCompatible
  apply forall_congr'
  intro b
  dsimp only
  have T := arithmeticLabeledAtlas_terminal_edge_isPullback hπ data H m j hj b
  rw [← cancel_epi T.isoPullback.hom]
  simp only [← Category.assoc, IsPullback.isoPullback_hom_fst,
    IsPullback.isoPullback_hom_snd]

end FLT.Mazur.WeierstrassDividedDepth
