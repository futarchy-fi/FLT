/-
Copyright (c) 2026 krandder. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: krandder
-/
module

public import FLT.Mazur.ProjectiveLineEndpointReversal
public import FLT.Mazur.WeierstrassDividedFinalZeroExterior
public import FLT.Mazur.WeierstrassDividedFinalBranchChains
public import FLT.Mazur.WeierstrassDividedZeroCycleIndices

/-!
# The actual cyclic component list at start zero with split terminal conic

Start with the exterior, reverse the first chain towards the terminal node,
then follow the second chain outwards. The endpoint convention is exactly
zero on component i and infinity on its cyclic successor.
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
  (hp : 2 * (start + s + 1) < depth)
local notation "K" => ResidueField R
local notation "p" => pullback.fst (Spec.map (CommRingCat.ofHom (algebraMap R K)))
  (finiteGlobalStructure hπ data (s + 1) hs)
local notation "ρ" => Iso.hom (ProjectiveLine.endpointReversalOverIso K)
local notation "C" => finalBranchComponent hπ data D s hs hk hp
local notation "N" => finalNodeOverSection hπ data D s hs hk hp

/-- The complete cyclic list of actual projective components over the residue field. -/
def zeroSplitCycleComponent (i : Fin (2 * s + 3)) :
    PolygonPinching.component K ⟶ Over.mk p :=
  if i.val = 0 then finalZeroExteriorOverComponent hπ data D s hs hstart hk
  else if h : i.val ≤ s + 1 then ρ ≫ C ⟨i.val - 1, by omega⟩ 0
  else C ⟨2 * s + 2 - i.val, by omega⟩ 1

/-- Position zero is the entire original exterior, with its original ordered endpoints. -/
theorem zeroSplitCycleComponent_exterior :
    zeroSplitCycleComponent hπ data D s hs hstart hk hp 0 =
      finalZeroExteriorOverComponent hπ data D s hs hstart hk := by
  simp only [zeroSplitCycleComponent, Fin.val_zero, ite_true]

/-- Every original first-chain component occurs with its two endpoints reversed. -/
theorem zeroSplitCycleComponent_first (j : Fin (s + 1)) :
    zeroSplitCycleComponent hπ data D s hs hstart hk hp ⟨j.val + 1, by omega⟩ =
      ρ ≫ C j 0 := by
  rw [zeroSplitCycleComponent, ite_eq_right (show ¬j.val + 1 = 0 by omega),
    dite_eq_left (show j.val + 1 ≤ s + 1 by omega)]
  rfl

/-- Every original second-chain component occurs in its unchanged parameterization. -/
theorem zeroSplitCycleComponent_second (j : Fin (s + 1)) :
    zeroSplitCycleComponent hπ data D s hs hstart hk hp ⟨2 * s + 2 - j.val, by omega⟩ =
      C j 1 := by
  rw [zeroSplitCycleComponent, ite_eq_right (show ¬2 * s + 2 - j.val = 0 by omega),
    dite_eq_right (show ¬2 * s + 2 - j.val ≤ s + 1 by omega)]
  congr 1
  apply Fin.ext
  change 2 * s + 2 - (2 * s + 2 - j.val) = j.val
  omega

/-- The zero endpoint is precisely the original node at the same cyclic position. -/
@[reassoc] theorem zeroSplitCycleComponent_zero (i : Fin (2 * s + 3)) :
    ProjectiveLine.zeroSection K ≫ zeroSplitCycleComponent hπ data D s hs hstart hk hp i =
      N (zeroSplitCycleNodeIndex start s i) := by
  by_cases hi : i.val = 0
  · have he : i = 0 := Fin.ext hi
    subst i
    rw [zeroSplitCycleComponent_exterior,
      finalZeroExteriorOverComponent_zero hπ data D s hs hstart hk hp]
    rw [show (0 : Fin (2 * s + 3)) = ⟨(0 : Fin (s + 1)).val, by omega⟩ from rfl,
      zeroSplitCycleNodeIndex_first]
  · by_cases h : i.val ≤ s + 1
    · rw [zeroSplitCycleComponent, ite_eq_right hi, dite_eq_left h,
        ProjectiveLine.zeroSection_endpointReversal_assoc, finalBranchComponent_infinity]
      congr 1
      by_cases hlt : i.val < s + 1
      · rw [finalBranchVertex,
          dite_eq_left (show i.val - 1 + 1 < s + 1 by omega),
          zeroSplitCycleNodeIndex, dite_eq_left hlt]
        congr 3
        apply Fin.ext
        change i.val - 1 + 1 = i.val
        omega
      · rw [finalBranchVertex,
          dite_eq_right (show ¬i.val - 1 + 1 < s + 1 by omega),
          zeroSplitCycleNodeIndex, dite_eq_right hlt, dite_eq_left (by omega)]
    · rw [zeroSplitCycleComponent, ite_eq_right hi, dite_eq_right h, finalBranchComponent_zero]
      congr 1
      rw [finalBranchVertex, dite_eq_left (show 2 * s + 2 - i.val < s + 1 by omega),
        zeroSplitCycleNodeIndex,
        dite_eq_right (by omega), dite_eq_right (by omega)]

/-- Infinity on the next component is that same original node, including the cyclic wrap. -/
@[reassoc] theorem zeroSplitCycleComponent_next_infinity (i : Fin (2 * s + 3)) :
    ProjectiveLine.infinitySection K ≫
        zeroSplitCycleComponent hπ data D s hs hstart hk hp
          (PolygonPinching.next (by omega) i) = N (zeroSplitCycleNodeIndex start s i) := by
  by_cases hi : i.val < s + 1
  · have hn : PolygonPinching.next (by omega) i =
        (⟨i.val + 1, by omega⟩ : Fin (2 * s + 3)) := by
      apply Fin.ext
      exact Nat.mod_eq_of_lt (by omega)
    rw [hn, zeroSplitCycleComponent_first hπ data D s hs hstart hk hp ⟨i.val, hi⟩,
      ProjectiveLine.infinitySection_endpointReversal_assoc, finalBranchComponent_zero,
      finalBranchVertex_retained]
    congr 1
    exact (zeroSplitCycleNodeIndex_first start s ⟨i.val, hi⟩).symm
  · by_cases hit : i.val = s + 1
    · have hn : PolygonPinching.next (by omega) i =
          (⟨2 * s + 2 - (⟨s, by omega⟩ : Fin (s + 1)).val, by omega⟩ :
            Fin (2 * s + 3)) := by
        apply Fin.ext
        change (i.val + 1) % (2 * s + 3) = _
        rw [Nat.mod_eq_of_lt (by omega)]
        change i.val + 1 = 2 * s + 2 - s
        omega
      rw [hn, zeroSplitCycleComponent_second, finalBranchComponent_infinity,
        finalBranchVertex_terminal]
      congr 1
      have he : i = ⟨s + 1, by omega⟩ := Fin.ext hit
      rw [he, zeroSplitCycleNodeIndex_terminal]
    · by_cases hilast : i.val = 2 * s + 2
      · have hn : PolygonPinching.next (by omega) i = (0 : Fin (2 * s + 3)) := by
          apply Fin.ext
          simp only [PolygonPinching.next_val, Fin.val_zero]
          rw [show i.val + 1 = 2 * s + 3 by omega, Nat.mod_self]
        rw [hn, zeroSplitCycleComponent_exterior,
          finalZeroExteriorOverComponent_infinity hπ data D s hs hstart hk hp]
        congr 1
        have he : i = ⟨2 * s + 2 - (0 : Fin (s + 1)).val, by omega⟩ :=
          Fin.ext (by simpa using hilast)
        rw [he, zeroSplitCycleNodeIndex_second]
      · let j : Fin (s + 1) := ⟨2 * s + 1 - i.val, by omega⟩
        have hn : PolygonPinching.next (by omega) i =
            (⟨2 * s + 2 - j.val, by omega⟩ : Fin (2 * s + 3)) := by
          apply Fin.ext
          change (i.val + 1) % (2 * s + 3) = _
          rw [Nat.mod_eq_of_lt (by omega)]
          change i.val + 1 = 2 * s + 2 - (2 * s + 1 - i.val)
          omega
        rw [hn, zeroSplitCycleComponent_second, finalBranchComponent_infinity]
        congr 1
        rw [finalBranchVertex,
          dite_eq_left (show (2 * s + 1 - i.val) + 1 < s + 1 by omega),
          zeroSplitCycleNodeIndex, dite_eq_right hi, dite_eq_right hit]
        congr 3
        apply Fin.ext
        change (2 * s + 1 - i.val) + 1 = 2 * s + 2 - i.val
        omega

/-- The actual component maps satisfy the specified polygon endpoint convention. -/
theorem zeroSplitCycleComponent_endpoints (i : Fin (2 * s + 3)) :
    ProjectiveLine.zeroSection K ≫ zeroSplitCycleComponent hπ data D s hs hstart hk hp i =
      ProjectiveLine.infinitySection K ≫
        zeroSplitCycleComponent hπ data D s hs hstart hk hp
          (PolygonPinching.next (by omega) i) := by
  rw [zeroSplitCycleComponent_zero, zeroSplitCycleComponent_next_infinity]

end FLT.Mazur.WeierstrassDividedDepth
