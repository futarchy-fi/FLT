/-
Copyright (c) 2026 krandder. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: krandder
-/
module

public import FLT.Mazur.ProjectiveLineEndpointReversal
public import FLT.Mazur.WeierstrassDividedEqualityComponentEndpoints
public import FLT.Mazur.WeierstrassDividedZeroEqualityCycleIndices

/-!
# The original component cycle at equality depth and start zero

The exterior is followed by the reversed first adjacent chain, the single
reversed terminal projective line, and the second adjacent chain in decreasing
order. The terminal line joins the retained attachments without adding a node.
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
  (hstart : start = 0) (hk : 2 * (start + s + 1) ≤ depth)
  (hp : 2 * (start + s + 1) = depth)
local notation "K" => ResidueField R
local notation "p" => pullback.fst (Spec.map (CommRingCat.ofHom (algebraMap R K)))
  (finiteGlobalStructure hπ data (s + 1) hs)
local notation "ρ" => Iso.hom (ProjectiveLine.endpointReversalOverIso K)
local notation "C" => finalAdjacentOverComponent hπ data D s hs hk
local notation "N" => equalityNodeOverSection hπ data D s hs hk

/-- The complete equality-depth cycle in the original finite model. -/
def zeroEqualityCycleComponent (i : Fin (2 * s + 2)) :
    PolygonPinching.component K ⟶ Over.mk p :=
  if h0 : i.val = 0 then finalZeroExteriorOverComponent hπ data D s hs hstart hk
  else if h : i.val ≤ s then ρ ≫ C ⟨i.val - 1, by omega⟩ 0
  else if ht : i.val = s + 1 then ρ ≫ equalityTerminalOverComponent hπ data D s hs hk hp
  else C ⟨2 * s + 1 - i.val, by omega⟩ 1

/-- The first position retains the original exterior parameterization. -/
theorem zeroEqualityCycleComponent_exterior :
    zeroEqualityCycleComponent hπ data D s hs hstart hk hp 0 =
      finalZeroExteriorOverComponent hπ data D s hs hstart hk := by
  simp only [zeroEqualityCycleComponent, Fin.val_zero, dite_true]

/-- First-chain components occur with their ordered endpoints reversed. -/
theorem zeroEqualityCycleComponent_first (j : Fin s) :
    zeroEqualityCycleComponent hπ data D s hs hstart hk hp ⟨j.val + 1, by omega⟩ =
      ρ ≫ C j 0 := by
  rw [zeroEqualityCycleComponent, dite_eq_right (show ¬j.val + 1 = 0 by omega),
    dite_eq_left (show j.val + 1 ≤ s by omega)]
  rfl

/-- There is exactly one terminal position, containing the entire projective line. -/
theorem zeroEqualityCycleComponent_terminal :
    zeroEqualityCycleComponent hπ data D s hs hstart hk hp ⟨s + 1, by omega⟩ =
      ρ ≫ equalityTerminalOverComponent hπ data D s hs hk hp := by
  rw [zeroEqualityCycleComponent, dite_eq_right (show ¬s + 1 = 0 by omega),
    dite_eq_right (show ¬s + 1 ≤ s by omega), dite_eq_left rfl]

/-- Second-chain components retain their parameterization and occur in decreasing order. -/
theorem zeroEqualityCycleComponent_second (j : Fin s) :
    zeroEqualityCycleComponent hπ data D s hs hstart hk hp ⟨2 * s + 1 - j.val, by omega⟩ =
      C j 1 := by
  rw [zeroEqualityCycleComponent, dite_eq_right (show ¬2 * s + 1 - j.val = 0 by omega),
    dite_eq_right (show ¬2 * s + 1 - j.val ≤ s by omega),
    dite_eq_right (show ¬2 * s + 1 - j.val = s + 1 by omega)]
  congr 1
  apply Fin.ext
  change 2 * s + 1 - (2 * s + 1 - j.val) = j.val
  omega

/-- Zero of each component is the original attachment at its cyclic position. -/
@[reassoc] theorem zeroEqualityCycleComponent_zero (i : Fin (2 * s + 2)) :
    ProjectiveLine.zeroSection K ≫ zeroEqualityCycleComponent hπ data D s hs hstart hk hp i =
      N (zeroEqualityCycleNodeIndex start s i) := by
  by_cases hi : i.val = 0
  · have he : i = 0 := Fin.ext hi
    subst i
    rw [zeroEqualityCycleComponent_exterior, equalityZeroExteriorOverComponent_zero]
    rfl
  · by_cases h : i.val ≤ s
    · rw [zeroEqualityCycleComponent, dite_eq_right hi, dite_eq_left h,
        ProjectiveLine.zeroSection_endpointReversal_assoc,
        equalityAdjacentOverComponent_infinity]
      congr 1
      rw [zeroEqualityCycleNodeIndex, dite_eq_left (by omega)]
      congr 2
      apply Fin.ext
      change i.val - 1 + 1 = i.val
      omega
    · by_cases ht : i.val = s + 1
      · have he : i = ⟨s + 1, by omega⟩ := Fin.ext ht
        rw [he, zeroEqualityCycleComponent_terminal,
          ProjectiveLine.zeroSection_endpointReversal_assoc,
          equalityTerminalOverComponent_infinity]
        congr 1
        rw [zeroEqualityCycleNodeIndex, dite_eq_right (by omega)]
        congr 2
        apply Fin.ext
        change s = 2 * s + 1 - (s + 1)
        omega
      · rw [zeroEqualityCycleComponent, dite_eq_right hi, dite_eq_right h, dite_eq_right ht,
          equalityAdjacentOverComponent_zero]
        rw [zeroEqualityCycleNodeIndex, dite_eq_right (by omega)]

/-- Infinity on the successor is the same attachment, including the cyclic wrap. -/
@[reassoc] theorem zeroEqualityCycleComponent_next_infinity (i : Fin (2 * s + 2)) :
    ProjectiveLine.infinitySection K ≫
        zeroEqualityCycleComponent hπ data D s hs hstart hk hp
          (PolygonPinching.next (by omega) i) = N (zeroEqualityCycleNodeIndex start s i) := by
  by_cases hi : i.val < s
  · have hn : PolygonPinching.next (by omega) i =
        (⟨i.val + 1, by omega⟩ : Fin (2 * s + 2)) := by
      apply Fin.ext
      exact Nat.mod_eq_of_lt (by omega)
    rw [hn, zeroEqualityCycleComponent_first hπ data D s hs hstart hk hp ⟨i.val, hi⟩,
      ProjectiveLine.infinitySection_endpointReversal_assoc, equalityAdjacentOverComponent_zero]
    congr 1
    exact (zeroEqualityCycleNodeIndex_first start s ⟨i.val, by omega⟩).symm
  · by_cases hit : i.val = s
    · have hn : PolygonPinching.next (by omega) i =
          (⟨s + 1, by omega⟩ : Fin (2 * s + 2)) := by
        apply Fin.ext
        change (i.val + 1) % (2 * s + 2) = s + 1
        rw [hit, Nat.mod_eq_of_lt (by omega)]
      rw [hn, zeroEqualityCycleComponent_terminal,
        ProjectiveLine.infinitySection_endpointReversal_assoc, equalityTerminalOverComponent_zero]
      congr 1
      have he : i = ⟨s, by omega⟩ := Fin.ext hit
      rw [he, zeroEqualityCycleNodeIndex_first start s ⟨s, by omega⟩]
    · by_cases hilast : i.val = 2 * s + 1
      · have hn : PolygonPinching.next (by omega) i = (0 : Fin (2 * s + 2)) := by
          apply Fin.ext
          simp only [PolygonPinching.next_val, Fin.val_zero]
          rw [show i.val + 1 = 2 * s + 2 by omega, Nat.mod_self]
        rw [hn, zeroEqualityCycleComponent_exterior, equalityZeroExteriorOverComponent_infinity]
        congr 1
        have he : i = ⟨2 * s + 1 - (0 : Fin (s + 1)).val, by omega⟩ :=
          Fin.ext (by simpa using hilast)
        rw [he, zeroEqualityCycleNodeIndex_second]
      · let j : Fin s := ⟨2 * s - i.val, by omega⟩
        have hn : PolygonPinching.next (by omega) i =
            (⟨2 * s + 1 - j.val, by omega⟩ : Fin (2 * s + 2)) := by
          apply Fin.ext
          change (i.val + 1) % (2 * s + 2) = _
          rw [Nat.mod_eq_of_lt (by omega)]
          change i.val + 1 = 2 * s + 1 - (2 * s - i.val)
          omega
        rw [hn, zeroEqualityCycleComponent_second, equalityAdjacentOverComponent_infinity]
        congr 1
        rw [zeroEqualityCycleNodeIndex, dite_eq_right (by omega)]
        congr 2
        apply Fin.ext
        change (2 * s - i.val) + 1 = 2 * s + 1 - i.val
        omega

/-- The actual maps satisfy the specified cyclic pinching convention. -/
theorem zeroEqualityCycleComponent_endpoints (i : Fin (2 * s + 2)) :
    ProjectiveLine.zeroSection K ≫ zeroEqualityCycleComponent hπ data D s hs hstart hk hp i =
      ProjectiveLine.infinitySection K ≫
        zeroEqualityCycleComponent hπ data D s hs hstart hk hp
          (PolygonPinching.next (by omega) i) := by
  rw [zeroEqualityCycleComponent_zero, zeroEqualityCycleComponent_next_infinity]

end FLT.Mazur.WeierstrassDividedDepth
