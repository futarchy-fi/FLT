/-
Copyright (c) 2026 krandder. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: krandder
-/
module

public import FLT.Mazur.ProjectiveLineEndpointReversal
public import FLT.Mazur.WeierstrassDividedPositiveEqualityBranches
public import FLT.Mazur.WeierstrassDividedEqualityInitialExterior
public import FLT.Mazur.WeierstrassDividedPositiveEqualityCycleIndices

/-!
# The original component cycle at equality depth and positive start

The exterior is followed by the reversed first complete branch, the single
reversed terminal projective line, and the second complete branch in decreasing
order. Both initial projective components occur in these branches.
The terminal line joins the retained attachments without adding a node.
-/

@[expose] public noncomputable section
open AlgebraicGeometry CategoryTheory Limits IsLocalRing
namespace FLT.Mazur.WeierstrassDividedDepth
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
universe u
variable {R : Type u} [CommRing R] [IsDomain R] [IsBezout R] [IsLocalRing R]
  {W : WeierstrassCurve R} {π : R} (hπ : π ≠ 0) {start n depth : ℕ}
  (data : (i : Fin (n + 1)) → Data W π (start + i.val))
  (D : SplitNodeDepth W π depth) (s : ℕ) (hs : s + 1 ≤ n)
  (hstart : 0 < start) (hk : 2 * (start + s + 1) ≤ depth)
  (hp : 2 * (start + s + 1) = depth)
local notation "K" => ResidueField R
local notation "p" => pullback.fst (Spec.map (CommRingCat.ofHom (algebraMap R K)))
  (finiteGlobalStructure hπ data (s + 1) hs)
local notation "ρ" => Iso.hom (ProjectiveLine.endpointReversalOverIso K)
local notation "C" => positiveEqualityBranchComponent hπ data D s hs hstart hk
local notation "N" => equalityNodeOverSection hπ data D s hs hk

/-- The complete equality-depth cycle in the original finite model. -/
def positiveEqualityCycleComponent (i : Fin (2 * s + 4)) :
    PolygonPinching.component K ⟶ Over.mk p :=
  if h0 : i.val = 0 then equalityInitialExteriorOverComponent hπ data D s hs hstart hk
  else if h : i.val ≤ s + 1 then ρ ≫ C ⟨i.val - 1, by omega⟩ 0
  else if ht : i.val = s + 2 then ρ ≫ equalityTerminalOverComponent hπ data D s hs hk hp
  else C ⟨2 * s + 3 - i.val, by omega⟩ 1

/-- The first position retains the original exterior parameterization. -/
theorem positiveEqualityCycleComponent_exterior :
    positiveEqualityCycleComponent hπ data D s hs hstart hk hp 0 =
      equalityInitialExteriorOverComponent hπ data D s hs hstart hk := by
  simp only [positiveEqualityCycleComponent, Fin.val_zero, dite_true]

/-- First-chain components occur with their ordered endpoints reversed. -/
theorem positiveEqualityCycleComponent_first (j : Fin (s + 1)) :
    positiveEqualityCycleComponent hπ data D s hs hstart hk hp ⟨j.val + 1, by omega⟩ =
      ρ ≫ C j 0 := by
  rw [positiveEqualityCycleComponent, dite_eq_right (show ¬j.val + 1 = 0 by omega),
    dite_eq_left (show j.val + 1 ≤ s + 1 by omega)]
  rfl

/-- There is exactly one terminal position, containing the entire projective line. -/
theorem positiveEqualityCycleComponent_terminal :
    positiveEqualityCycleComponent hπ data D s hs hstart hk hp ⟨s + 2, by omega⟩ =
      ρ ≫ equalityTerminalOverComponent hπ data D s hs hk hp := by
  rw [positiveEqualityCycleComponent, dite_eq_right (show ¬s + 2 = 0 by omega),
    dite_eq_right (show ¬s + 2 ≤ s + 1 by omega), dite_eq_left rfl]

/-- Second-chain components retain their parameterization and occur in decreasing order. -/
theorem positiveEqualityCycleComponent_second (j : Fin (s + 1)) :
    positiveEqualityCycleComponent hπ data D s hs hstart hk hp ⟨2 * s + 3 - j.val, by omega⟩ =
      C j 1 := by
  rw [positiveEqualityCycleComponent, dite_eq_right (show ¬2 * s + 3 - j.val = 0 by omega),
    dite_eq_right (show ¬2 * s + 3 - j.val ≤ s + 1 by omega),
    dite_eq_right (show ¬2 * s + 3 - j.val = s + 2 by omega)]
  congr 1
  apply Fin.ext
  change 2 * s + 3 - (2 * s + 3 - j.val) = j.val
  omega

/-- Zero of each component is the original attachment at its cyclic position. -/
@[reassoc] theorem positiveEqualityCycleComponent_zero (i : Fin (2 * s + 4)) :
    ProjectiveLine.zeroSection K ≫ positiveEqualityCycleComponent hπ data D s hs hstart hk hp i =
      N (positiveEqualityCycleNodeIndex start s hstart i) := by
  by_cases hi : i.val = 0
  · have he : i = 0 := Fin.ext hi
    subst i
    rw [positiveEqualityCycleComponent_exterior, equalityInitialExteriorOverComponent_zero]
    rfl
  · by_cases h : i.val ≤ s + 1
    · rw [positiveEqualityCycleComponent, dite_eq_right hi, dite_eq_left h,
        ProjectiveLine.zeroSection_endpointReversal_assoc,
        positiveEqualityBranchComponent_infinity]
      congr 1
      rw [positiveEqualityCycleNodeIndex, dite_eq_left (by omega)]
      congr 1
      apply Fin.ext
      change i.val - 1 + 1 = i.val
      omega
    · by_cases ht : i.val = s + 2
      · have he : i = ⟨s + 2, by omega⟩ := Fin.ext ht
        rw [he, positiveEqualityCycleComponent_terminal,
          ProjectiveLine.zeroSection_endpointReversal_assoc,
          positiveEqualityTerminal_infinity hπ data D s hs hstart hk hp]
        congr 1
        rw [positiveEqualityCycleNodeIndex, dite_eq_right (by omega)]
        congr 1
        apply Fin.ext
        change s + 1 = 2 * s + 3 - (s + 2)
        omega
      · rw [positiveEqualityCycleComponent, dite_eq_right hi, dite_eq_right h, dite_eq_right ht,
          positiveEqualityBranchComponent_zero]
        rw [positiveEqualityCycleNodeIndex, dite_eq_right (by omega)]

/-- Infinity on the successor is the same attachment, including the cyclic wrap. -/
@[reassoc] theorem positiveEqualityCycleComponent_next_infinity (i : Fin (2 * s + 4)) :
    ProjectiveLine.infinitySection K ≫
        positiveEqualityCycleComponent hπ data D s hs hstart hk hp
          (PolygonPinching.next (by omega) i) =
      N (positiveEqualityCycleNodeIndex start s hstart i) := by
  by_cases hi : i.val < s + 1
  · have hn : PolygonPinching.next (by omega) i =
        (⟨i.val + 1, by omega⟩ : Fin (2 * s + 4)) := by
      apply Fin.ext
      exact Nat.mod_eq_of_lt (by omega)
    rw [hn, positiveEqualityCycleComponent_first hπ data D s hs hstart hk hp ⟨i.val, hi⟩,
      ProjectiveLine.infinitySection_endpointReversal_assoc, positiveEqualityBranchComponent_zero]
    congr 1
    exact (positiveEqualityCycleNodeIndex_first start s hstart ⟨i.val, by omega⟩).symm
  · by_cases hit : i.val = s + 1
    · have hn : PolygonPinching.next (by omega) i =
          (⟨s + 2, by omega⟩ : Fin (2 * s + 4)) := by
        apply Fin.ext
        change (i.val + 1) % (2 * s + 4) = s + 2
        rw [hit, Nat.mod_eq_of_lt (by omega)]
      rw [hn, positiveEqualityCycleComponent_terminal,
        ProjectiveLine.infinitySection_endpointReversal_assoc,
        positiveEqualityTerminal_zero hπ data D s hs hstart hk hp]
      congr 1
      have he : i = ⟨s + 1, by omega⟩ := Fin.ext hit
      rw [he, positiveEqualityCycleNodeIndex_first start s hstart ⟨s + 1, by omega⟩]
    · by_cases hilast : i.val = 2 * s + 3
      · have hn : PolygonPinching.next (by omega) i = (0 : Fin (2 * s + 4)) := by
          apply Fin.ext
          simp only [PolygonPinching.next_val, Fin.val_zero]
          rw [show i.val + 1 = 2 * s + 4 by omega, Nat.mod_self]
        rw [hn, positiveEqualityCycleComponent_exterior,
          equalityInitialExteriorOverComponent_infinity]
        congr 1
        have he : i = ⟨2 * s + 3 - (0 : Fin (s + 2)).val, by omega⟩ :=
          Fin.ext (by simpa using hilast)
        rw [he, positiveEqualityCycleNodeIndex_second, positiveEqualityBranchNode_initial]
      · let j : Fin (s + 1) := ⟨2 * s + 2 - i.val, by omega⟩
        have hn : PolygonPinching.next (by omega) i =
            (⟨2 * s + 3 - j.val, by omega⟩ : Fin (2 * s + 4)) := by
          apply Fin.ext
          change (i.val + 1) % (2 * s + 4) = _
          rw [Nat.mod_eq_of_lt (by omega)]
          change i.val + 1 = 2 * s + 3 - (2 * s + 2 - i.val)
          omega
        rw [hn, positiveEqualityCycleComponent_second, positiveEqualityBranchComponent_infinity]
        congr 1
        rw [positiveEqualityCycleNodeIndex, dite_eq_right (by omega)]
        congr 1
        apply Fin.ext
        change (2 * s + 2 - i.val) + 1 = 2 * s + 3 - i.val
        omega

/-- The actual maps satisfy the specified cyclic pinching convention. -/
theorem positiveEqualityCycleComponent_endpoints (i : Fin (2 * s + 4)) :
    ProjectiveLine.zeroSection K ≫ positiveEqualityCycleComponent hπ data D s hs hstart hk hp i =
      ProjectiveLine.infinitySection K ≫
        positiveEqualityCycleComponent hπ data D s hs hstart hk hp
          (PolygonPinching.next (by omega) i) := by
  rw [positiveEqualityCycleComponent_zero, positiveEqualityCycleComponent_next_infinity]

end FLT.Mazur.WeierstrassDividedDepth
