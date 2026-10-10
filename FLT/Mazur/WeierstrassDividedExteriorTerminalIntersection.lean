/-
Copyright (c) 2026 krandder. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: krandder
-/
module

public import FLT.Mazur.WeierstrassDividedExteriorTerminalExclusions
public import FLT.Mazur.WeierstrassDividedZeroExteriorParameterIntersection

/-!
# Exact exterior intersections with the terminal pair at the first stage

When there are no intervening retained components, the two terminal components
meet the exterior at its two original ordered nodes.
-/

@[expose] public noncomputable section
open AlgebraicGeometry CategoryTheory IsLocalRing
namespace FLT.Mazur.WeierstrassDividedDepth
open WeierstrassModificationX
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
universe u
variable {R : Type u} [CommRing R] [IsDomain R] [IsBezout R] [IsLocalRing R]
  {W : WeierstrassCurve R} {π : R} (hπ : π ≠ 0) {start n depth : ℕ}
  (data : (i : Fin (n + 1)) → Data W π (start + i.val))
  (D : SplitNodeDepth W π depth) (hs : 0 + 1 ≤ n)
  (hstart : start = 0) (hk : 2 * (start + 0 + 1) ≤ depth)
  (hp : 2 * (start + 0 + 1) < depth)
local notation "K" => ResidueField R
local notation "E" => finalZeroExteriorComponent hπ data D 0 hs hstart hk
local notation "d" => data (Fin.mk (0 + 1) (Nat.lt_succ_of_le hs))
local notation "c" => residue R (Data.b6 d)
local notation "hc" => Iff.mpr (residue_eq_zero_iff _)
  (WeierstrassDilatation.divided_constant_mem D (start + 0 + 1) hp
    (Data.b6 d) (Data.factor6 d))

/-- The first complete terminal component meets the exterior at the original first node. -/
theorem finalZeroExteriorComponent_first_terminal_inter :
    Set.range E ∩ Set.range (finalTerminalComponent hπ data D 0 hs hk hp 0) =
      Set.range (finalNodeSection hπ data D 0 hs hk hp (.inl (.inr (0, 0)))) := by
  rw [ProjectiveLine.map_range_left_infinity (finalTerminalComponent hπ data D 0 hs hk hp 0),
    finalTerminalComponent_infinity, Set.inter_union_distrib_left,
    Set.disjoint_iff_inter_eq_empty.mp
      (finalZeroExteriorComponent_terminal_node_disjoint hπ data D 0 hs hk hp hstart),
    Set.union_empty, finalTerminalComponent_zero_depth hπ data D 0 hs hk hp (by omega)]
  change Set.range E ∩ Set.range (ProjectiveLine.left K ≫
    terminalZeroFirstComponent hπ data D 0 hs (by omega) hk hp) = _
  rw [terminalZeroFirstComponent_left]
  have hrange : Set.range ((conicZeroAffineIso c hc).hom ≫
      terminalZeroConicFirstParameter hπ data D 0 hs hstart hk) =
      Set.range (terminalZeroConicFirstParameter hπ data D 0 hs hstart hk) :=
    (conicZeroAffineIso c hc).hom.homeomorph.surjective.range_comp
      (terminalZeroConicFirstParameter hπ data D 0 hs hstart hk)
  rw [hrange]
  rw [terminalZeroConicFirstParameter_retained, finalZeroExteriorComponent,
    eqToHom_refl, Category.comp_id, zeroRetainedOrientedToGlobal_range,
    zeroRetainedExterior_first_parameter_inter]
  change _ = Set.range (retainedNodeSectionAt hπ data D (0 + 1 + 0) hs 0 (by omega) hk 0)
  rw [retainedNodeSectionAt_original hπ data D 0 hs 0 hs,
    orderedRetainedSection_zero hπ data D 0 hs 0 hs hk (by omega)]
  rfl

/-- The opposite terminal component meets the exterior at the original second node. -/
theorem finalZeroExteriorComponent_second_terminal_inter :
    Set.range E ∩ Set.range (finalTerminalComponent hπ data D 0 hs hk hp 1) =
      Set.range (finalNodeSection hπ data D 0 hs hk hp (.inl (.inr (0, 1)))) := by
  rw [ProjectiveLine.map_range_left_infinity (finalTerminalComponent hπ data D 0 hs hk hp 1),
    finalTerminalComponent_infinity, Set.inter_union_distrib_left,
    Set.disjoint_iff_inter_eq_empty.mp
      (finalZeroExteriorComponent_terminal_node_disjoint hπ data D 0 hs hk hp hstart),
    Set.union_empty, finalTerminalComponent_zero_depth hπ data D 0 hs hk hp (by omega)]
  change Set.range E ∩ Set.range (ProjectiveLine.left K ≫
    terminalZeroSecondComponent hπ data D 0 hs (by omega) hk hp) = _
  rw [terminalZeroSecondComponent_left]
  have hrange : Set.range ((conicZeroAffineIso c hc).hom ≫
      terminalZeroConicSecondParameter hπ data D 0 hs hstart hk) =
      Set.range (terminalZeroConicSecondParameter hπ data D 0 hs hstart hk) :=
    (conicZeroAffineIso c hc).hom.homeomorph.surjective.range_comp
      (terminalZeroConicSecondParameter hπ data D 0 hs hstart hk)
  rw [hrange]
  rw [terminalZeroConicSecondParameter_retained, finalZeroExteriorComponent,
    eqToHom_refl, Category.comp_id, zeroRetainedOrientedToGlobal_range,
    zeroRetainedExterior_second_parameter_inter]
  change _ = Set.range (retainedNodeSectionAt hπ data D (0 + 1 + 0) hs 0 (by omega) hk 1)
  rw [retainedNodeSectionAt_original hπ data D 0 hs 0 hs,
    orderedRetainedSection_zero hπ data D 0 hs 0 hs hk (by omega)]
  rfl

end FLT.Mazur.WeierstrassDividedDepth
