/-
Copyright (c) 2026 krandder. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: krandder
-/
module

public import FLT.Mazur.WeierstrassDividedLaurentTerminalOpenExclusions
public import FLT.Mazur.WeierstrassDividedOlderGlobalZeroNodeBoundaries
public import FLT.Mazur.WeierstrassDividedZeroEqualityAtlasTerminalSeparation

/-!
# The complete scale-zero terminal component misses infinity

The full original conic has empty infinity preimage. Its nonempty open in the
terminal projective line excludes the entire component and Laurent chart.
-/

@[expose] public noncomputable section
open AlgebraicGeometry CategoryTheory IsLocalRing
namespace FLT.Mazur.WeierstrassDividedDepth
open WeierstrassSuccessiveX
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
universe u
variable {R : Type u} [CommRing R] [IsDomain R] [IsBezout R] [IsLocalRing R]
  {W : WeierstrassCurve R} {π : R} (hπ : π ≠ 0) {start n depth : ℕ}
  (data : (i : Fin (n + 1)) → Data W π (start + i.val))
  (D : SplitNodeDepth W π depth) (s : ℕ) (hs : s + 1 ≤ n)
  (hk : 2 * (start + s + 1) ≤ depth) (hp : 2 * (start + s + 1) = depth)
  (hzero : start + s = 0)
local notation "K" => ResidueField R
local notation "C" => laurentTerminalOriginalConic hπ data D s hs hk
local notation "F" => laurentTerminalProjectiveComponent hπ data D s hs hk hp
local notation "m" => globalTensorAtlasMap hπ data K (s + 1) hs

/-- At scale zero the original conic is the complete retained initial conic. -/
theorem laurentTerminalOriginalConic_zero_retained :
    C = olderGlobalZeroConic hπ data D s hs 0 hs hzero hk := by
  rw [laurentTerminalOriginalConic_zero hπ data D s hs hk hzero]
  unfold olderGlobalZeroConic olderGlobalZeroSuccessiveChart
  rw [olderGlobalTensorChart_zero_retention]
  simp only [zeroResidueConicImmersion, Category.assoc]

include hzero in
/-- The entire scale-zero terminal component has no point in the infinity chart. -/
theorem laurentTerminalProjectiveComponent_zero_infinity_disjoint :
    Disjoint (Set.range F) (Set.range (m 0)) := by
  apply laurentTerminalProjectiveComponent_disjoint_of_conic hπ data D s hs hk hp
  rw [laurentTerminalOriginalConic_zero_retained hπ data D s hs hk hzero]
  apply Set.disjoint_left.mpr
  rintro _ ⟨z, rfl⟩ hz
  have H := olderGlobalZeroConic_infinity_preimage_empty hπ data D s hs 0 hs hzero hk
  have he : z ∈ olderGlobalZeroConic hπ data D s hs 0 hs hzero hk ⁻¹'
      Set.range (finiteInfinityTensorChart hπ data K (s + 1 + 0) hs) := hz
  rw [H] at he
  exact he

include D hk hp hzero in
/-- The whole Laurent atlas object is disjoint from infinity at scale zero as well. -/
theorem zeroEqualityAtlas_zero_terminal_infinity_disjoint :
    Disjoint (Set.range (m (Fin.succ 0))) (Set.range (m 0)) :=
  (laurentTerminalProjectiveComponent_zero_infinity_disjoint
    hπ data D s hs hk hp hzero).mono_left
      (terminalLaurentAtlas_range_subset_component hπ data D s hs hk hp)

end FLT.Mazur.WeierstrassDividedDepth
