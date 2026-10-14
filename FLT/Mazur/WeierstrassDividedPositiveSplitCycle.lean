/-
Copyright (c) 2026 krandder. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: krandder
-/
module

public import FLT.Mazur.ProjectiveLineEndpointReversal
public import FLT.Mazur.WeierstrassDividedPositiveSplitBranches
public import FLT.Mazur.WeierstrassDividedPositiveSplitCycleIndices

/-!
# The complete original positive-start strict component cycle

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
  (hstart : 0 < start) (hk : 2 * (start + s + 1) ≤ depth)
  (hp : 2 * (start + s + 1) < depth)
local notation "K" => ResidueField R
local notation "p" => pullback.fst (Spec.map (CommRingCat.ofHom (algebraMap R K)))
  (finiteGlobalStructure hπ data (s + 1) hs)
local notation "ρ" => Iso.hom (ProjectiveLine.endpointReversalOverIso K)
local notation "C" => positiveSplitBranchComponent hπ data D s hs hstart hk hp
local notation "N" => finalNodeOverSection hπ data D s hs hk hp

/-- The complete cyclic list of actual projective components over the residue field. -/
def positiveSplitCycleComponent (i : Fin (2 * s + 5)) :
    PolygonPinching.component K ⟶ Over.mk p :=
  if i.val = 0 then equalityInitialExteriorOverComponent hπ data D s hs hstart hk
  else if h : i.val ≤ s + 2 then ρ ≫ C ⟨i.val - 1, by omega⟩ 0
  else C ⟨2 * s + 4 - i.val, by omega⟩ 1

/-- Position zero is the entire original exterior, with its original ordered endpoints. -/
theorem positiveSplitCycleComponent_exterior :
    positiveSplitCycleComponent hπ data D s hs hstart hk hp 0 =
      equalityInitialExteriorOverComponent hπ data D s hs hstart hk := by
  simp only [positiveSplitCycleComponent, Fin.val_zero, ite_true]

/-- Every original first-chain component occurs with its two endpoints reversed. -/
theorem positiveSplitCycleComponent_first (j : Fin (s + 2)) :
    positiveSplitCycleComponent hπ data D s hs hstart hk hp ⟨j.val + 1, by omega⟩ =
      ρ ≫ C j 0 := by
  rw [positiveSplitCycleComponent, ite_eq_right (show ¬j.val + 1 = 0 by omega),
    dite_eq_left (show j.val + 1 ≤ s + 2 by omega)]
  rfl

/-- Every original second-chain component occurs in its unchanged parameterization. -/
theorem positiveSplitCycleComponent_second (j : Fin (s + 2)) :
    positiveSplitCycleComponent hπ data D s hs hstart hk hp ⟨2 * s + 4 - j.val, by omega⟩ =
      C j 1 := by
  rw [positiveSplitCycleComponent, ite_eq_right (show ¬2 * s + 4 - j.val = 0 by omega),
    dite_eq_right (show ¬2 * s + 4 - j.val ≤ s + 2 by omega)]
  congr 1
  apply Fin.ext
  change 2 * s + 4 - (2 * s + 4 - j.val) = j.val
  omega

/-- The zero endpoint is precisely the original node at the same cyclic position. -/
@[reassoc] theorem positiveSplitCycleComponent_zero (i : Fin (2 * s + 5)) :
    ProjectiveLine.zeroSection K ≫ positiveSplitCycleComponent hπ data D s hs hstart hk hp i =
      N (positiveSplitCycleNodeIndex start s hstart i) := by
  by_cases hi : i.val = 0
  · have he : i = 0 := Fin.ext hi
    subst i
    rw [positiveSplitCycleComponent_exterior,
      positiveSplitExterior_zero hπ data D s hs hstart hk hp]
    rw [show (0 : Fin (2 * s + 5)) = ⟨(0 : Fin (s + 2)).val, by omega⟩ from rfl,
      positiveSplitCycleNodeIndex_first]
    rfl
  · by_cases h : i.val ≤ s + 2
    · rw [positiveSplitCycleComponent, ite_eq_right hi, dite_eq_left h,
        ProjectiveLine.zeroSection_endpointReversal_assoc, positiveSplitBranchComponent_infinity]
      congr 1
      have he : (⟨i.val - 1 + 1, by omega⟩ : Fin (s + 3)) =
          ⟨i.val, by omega⟩ := Fin.ext (by change i.val - 1 + 1 = i.val; omega)
      rw [he]
      by_cases hlt : i.val < s + 2
      · exact (positiveSplitCycleNodeIndex_first start s hstart ⟨i.val, hlt⟩).symm
      · have hit : i.val = s + 2 := by omega
        rw [positiveSplitBranchNode, dite_eq_right hlt,
          positiveSplitCycleNodeIndex, dite_eq_right hlt, dite_eq_left hit]
    · rw [positiveSplitCycleComponent, ite_eq_right hi, dite_eq_right h,
        positiveSplitBranchComponent_zero]
      congr 1
      rw [positiveSplitCycleNodeIndex, dite_eq_right (by omega), dite_eq_right (by omega),
        positiveSplitBranchNode_attachment]

/-- Infinity on the next component is that same original node, including the cyclic wrap. -/
@[reassoc] theorem positiveSplitCycleComponent_next_infinity (i : Fin (2 * s + 5)) :
    ProjectiveLine.infinitySection K ≫
        positiveSplitCycleComponent hπ data D s hs hstart hk hp
          (PolygonPinching.next (by omega) i) =
      N (positiveSplitCycleNodeIndex start s hstart i) := by
  by_cases hi : i.val < s + 2
  · have hn : PolygonPinching.next (by omega) i =
        (⟨i.val + 1, by omega⟩ : Fin (2 * s + 5)) := by
      apply Fin.ext
      exact Nat.mod_eq_of_lt (by omega)
    rw [hn, positiveSplitCycleComponent_first hπ data D s hs hstart hk hp ⟨i.val, hi⟩,
      ProjectiveLine.infinitySection_endpointReversal_assoc, positiveSplitBranchComponent_zero]
    congr 1
    exact (positiveSplitCycleNodeIndex_first start s hstart ⟨i.val, hi⟩).symm
  · by_cases hit : i.val = s + 2
    · have hn : PolygonPinching.next (by omega) i =
          (⟨2 * s + 4 - (⟨s + 1, by omega⟩ : Fin (s + 2)).val, by omega⟩ :
            Fin (2 * s + 5)) := by
        apply Fin.ext
        change (i.val + 1) % (2 * s + 5) = _
        rw [Nat.mod_eq_of_lt (by omega)]
        change i.val + 1 = 2 * s + 4 - (s + 1)
        omega
      rw [hn, positiveSplitCycleComponent_second, positiveSplitBranchComponent_infinity,
        positiveSplitBranchNode_terminal]
      congr 1
      have he : i = ⟨s + 2, by omega⟩ := Fin.ext hit
      rw [he, positiveSplitCycleNodeIndex_terminal]
    · by_cases hilast : i.val = 2 * s + 4
      · have hn : PolygonPinching.next (by omega) i = (0 : Fin (2 * s + 5)) := by
          apply Fin.ext
          simp only [PolygonPinching.next_val, Fin.val_zero]
          rw [show i.val + 1 = 2 * s + 5 by omega, Nat.mod_self]
        rw [hn, positiveSplitCycleComponent_exterior,
          positiveSplitExterior_infinity hπ data D s hs hstart hk hp]
        congr 1
        have he : i = ⟨2 * s + 4 - (0 : Fin (s + 2)).val, by omega⟩ :=
          Fin.ext (by simpa using hilast)
        rw [he, positiveSplitCycleNodeIndex_second]
        rfl
      · let j : Fin (s + 2) := ⟨2 * s + 3 - i.val, by omega⟩
        have hn : PolygonPinching.next (by omega) i =
            (⟨2 * s + 4 - j.val, by omega⟩ : Fin (2 * s + 5)) := by
          apply Fin.ext
          change (i.val + 1) % (2 * s + 5) = _
          rw [Nat.mod_eq_of_lt (by omega)]
          change i.val + 1 = 2 * s + 4 - (2 * s + 3 - i.val)
          omega
        rw [hn, positiveSplitCycleComponent_second, positiveSplitBranchComponent_infinity]
        congr 1
        rw [positiveSplitCycleNodeIndex, dite_eq_right hi, dite_eq_right hit,
          positiveSplitBranchNode_attachment start s hstart
            ⟨j.val + 1, by dsimp [j]; omega⟩]
        congr 2
        apply Fin.ext
        change (2 * s + 3 - i.val) + 1 = 2 * s + 4 - i.val
        omega

/-- The actual component maps satisfy the specified polygon endpoint convention. -/
theorem positiveSplitCycleComponent_endpoints (i : Fin (2 * s + 5)) :
    ProjectiveLine.zeroSection K ≫ positiveSplitCycleComponent hπ data D s hs hstart hk hp i =
      ProjectiveLine.infinitySection K ≫
        positiveSplitCycleComponent hπ data D s hs hstart hk hp
          (PolygonPinching.next (by omega) i) := by
  rw [positiveSplitCycleComponent_zero, positiveSplitCycleComponent_next_infinity]

end FLT.Mazur.WeierstrassDividedDepth
