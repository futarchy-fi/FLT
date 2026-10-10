/-
Copyright (c) 2026 krandder. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: krandder
-/
module

public import FLT.Mazur.WeierstrassDividedTerminalComponentInjectivity
public import FLT.Mazur.WeierstrassDividedTerminalCrossedIntersection
public import FLT.Mazur.WeierstrassDividedTerminalZeroCrossedIntersection
public import FLT.Mazur.WeierstrassDividedTerminalBranchesNodeIntersection
public import FLT.Mazur.WeierstrassDividedTerminalComponentRanges
public import FLT.Mazur.ProjectiveLineMapRange
public import FLT.Mazur.WeierstrassDividedTerminalComponents
public import FLT.Mazur.WeierstrassDividedTerminalZeroComponents

/-!
# Exact intersection of the complete terminal component pair

The full projective components meet precisely along the original terminal node
section. Crossed affine pieces and the ordered conic parameters are disjoint.
-/

@[expose] public noncomputable section
open AlgebraicGeometry CategoryTheory Limits IsLocalRing
namespace FLT.Mazur.WeierstrassDividedDepth
open WeierstrassModificationX
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
universe u
/-- Injective postcomposition preserves disjoint scheme images. -/
theorem componentRange_disjoint_postcomp {A B X Y : Scheme.{u}}
    (f : A ⟶ X) (g : B ⟶ X) (t : X ⟶ Y) (ht : Function.Injective t)
    (h : Disjoint (Set.range f) (Set.range g)) :
    Disjoint (Set.range (f ≫ t)) (Set.range (g ≫ t)) := by
  apply Set.disjoint_left.mpr
  rintro _ ⟨x, rfl⟩ ⟨y, hy⟩
  exact Set.disjoint_left.mp h ⟨x, rfl⟩ ⟨y, ht hy⟩

/-- Three empty affine intersections leave only the fourth intersection. -/
theorem componentRange_union_inter {X : Type u} (a b c d : Set X)
    (hac : Disjoint a c) (had : Disjoint a d) (hbc : Disjoint b c) :
    (a ∪ b) ∩ (c ∪ d) = b ∩ d := by
  ext x
  constructor
  · rintro ⟨ha | hb, hc | hd⟩
    · exact (Set.disjoint_left.mp hac ha hc).elim
    · exact (Set.disjoint_left.mp had ha hd).elim
    · exact (Set.disjoint_left.mp hbc hb hc).elim
    · exact ⟨hb, hd⟩
  · exact fun h => ⟨Or.inr h.1, Or.inr h.2⟩

variable {R : Type u} [CommRing R] [IsDomain R] [IsBezout R] [IsLocalRing R]
  {W : WeierstrassCurve R} {π : R} (hπ : π ≠ 0) {start n depth : ℕ}
  (data : (i : Fin (n + 1)) → Data W π (start + i.val))
  (D : SplitNodeDepth W π depth) (j : ℕ) (hj : j + 1 ≤ n)
  (hk : 2 * (start + j + 1) ≤ depth) (hp : 2 * (start + j + 1) < depth)
local notation "d" => data (Fin.mk (j + 1) (Nat.lt_succ_of_le hj))
local notation "c" => residue R (Data.b6 d)
local notation "hc" => Iff.mpr (residue_eq_zero_iff _)
  (WeierstrassDilatation.divided_constant_mem D (start + j + 1) hp (Data.b6 d) (Data.factor6 d))

local notation "K" => ResidueField R

include hp in
/-- The full ordered terminal conic parameters remain disjoint in the global fiber. -/
theorem terminalConicParameters_disjoint (hk0 : 0 < start + j) :
    Disjoint (Set.range (terminalConicFirstParameter hπ data D j hj hk0 hk))
      (Set.range (terminalConicSecondParameter hπ data D j hj hk0 hk)) := by
  unfold terminalConicFirstParameter terminalConicSecondParameter
  apply componentRange_disjoint_postcomp
  · exact Scheme.Hom.injective _
  · exact WeierstrassSuccessiveX.conicParameters_disjoint_of_zero
      (W.map (residue R)) c (D.a₁_unit.map (residue R)) hc

include hp in
/-- The full ordered terminal conic parameters remain disjoint in the global fiber. -/
theorem terminalZeroConicParameters_disjoint (hk0 : start + j = 0) :
    Disjoint (Set.range (terminalZeroConicFirstParameter hπ data D j hj hk0 hk))
      (Set.range (terminalZeroConicSecondParameter hπ data D j hj hk0 hk)) := by
  unfold terminalZeroConicFirstParameter terminalZeroConicSecondParameter
  apply componentRange_disjoint_postcomp
  · exact Scheme.Hom.injective _
  · exact WeierstrassSuccessiveX.conicParameters_disjoint_of_zero
      (W.map (residue R)) c (D.a₁_unit.map (residue R)) hc

/-- The entire affine terminal branch intersection is the original node section. -/
theorem terminalConicBranches_range_inter :
    Set.range (terminalConicSecondBranch hπ data D j hj hk hp) ∩
        Set.range (terminalConicFirstBranch hπ data D j hj hk hp) =
      Set.range (terminalConicNodeSection hπ data D j hj hk hp) := by
  ext z
  constructor
  · rintro ⟨⟨x, rfl⟩, ⟨y, hy⟩⟩
    obtain ⟨v, hv, _⟩ := Scheme.exists_preimage_of_isPullback
      (terminalConicBranches_isPullback hπ data D j hj hk hp).flip x y hy.symm
    refine ⟨v, ?_⟩
    rw [← terminalConicSecondBranch_origin hπ data D j hj hk hp]
    exact congrArg (terminalConicSecondBranch hπ data D j hj hk hp) hv
  · rintro ⟨v, rfl⟩
    constructor
    · exact ⟨ProjectiveLine.chartZero K v, congrArg (fun f => f v)
        (terminalConicSecondBranch_origin hπ data D j hj hk hp)⟩
    · exact ⟨ProjectiveLine.chartZero K v, congrArg (fun f => f v)
        (terminalConicFirstBranch_origin hπ data D j hj hk hp)⟩

/-- The complete terminal pair meets exactly at its original common infinity node. -/
theorem terminalComponents_range_inter (hk0 : 0 < start + j) :
    Set.range (terminalFirstComponent hπ data D j hj hk0 hk hp) ∩
        Set.range (terminalSecondComponent hπ data D j hj hk0 hk hp) =
      Set.range (terminalConicNodeSection hπ data D j hj hk hp) := by
  rw [terminalFirstComponent_range, terminalSecondComponent_range]
  rw [componentRange_union_inter _ _ _ _
    (terminalConicParameters_disjoint hπ data D j hj hk hp hk0)
    (terminalConicFirstParameter_cross_disjoint hπ data D j hj hk0 hk hp)
    (terminalConicSecondParameter_cross_disjoint hπ data D j hj hk0 hk hp).symm]
  exact terminalConicBranches_range_inter hπ data D j hj hk hp

/-- The complete terminal pair meets exactly at its original common infinity node. -/
theorem terminalZeroComponents_range_inter (hk0 : start + j = 0) :
    Set.range (terminalZeroFirstComponent hπ data D j hj hk0 hk hp) ∩
        Set.range (terminalZeroSecondComponent hπ data D j hj hk0 hk hp) =
      Set.range (terminalConicNodeSection hπ data D j hj hk hp) := by
  rw [terminalZeroFirstComponent_range, terminalZeroSecondComponent_range]
  rw [componentRange_union_inter _ _ _ _
    (terminalZeroConicParameters_disjoint hπ data D j hj hk hp hk0)
    (terminalZeroConicFirstParameter_cross_disjoint hπ data D j hj hk0 hk hp)
    (terminalZeroConicSecondParameter_cross_disjoint hπ data D j hj hk0 hk hp).symm]
  exact terminalConicBranches_range_inter hπ data D j hj hk hp

end FLT.Mazur.WeierstrassDividedDepth
