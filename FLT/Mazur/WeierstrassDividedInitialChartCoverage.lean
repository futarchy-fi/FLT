/-
Copyright (c) 2026 krandder. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: krandder
-/
module

public import FLT.Mazur.WeierstrassDividedInitialExteriorOriented
public import FLT.Mazur.WeierstrassDividedInitialComponentRanges

/-!
# Complete initial-chart and exterior images at positive start

The original initial chart is the union of its incidence line and conic.
The oriented exterior retains the entire incidence line and infinity chart.
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
  (D : SplitNodeDepth W π depth) (j : ℕ) (hj : j ≤ n)
  (hstart : 0 < start) (hk : 2 * start ≤ depth)
local notation "K" => ResidueField R
local notation "d" => data (Fin.mk 0 (Nat.zero_lt_succ n))
local notation "α" => residue R W.a₁
local notation "c" => residue R (Data.b6 d)
local notation "g" => initialGlobalResidueFiberChart hπ data D j hj hstart hk

/-- Passing through the initial normal-form isomorphism preserves the whole original chart. -/
theorem initialGlobalResidueFiberChart_range :
    Set.range g = Set.range (globalInitialTensorChart hπ data K j hj) := by
  rw [initialGlobalResidueFiberChart]
  exact initialComponent_iso_comp_range
    (residueFiberIso D start hstart hk
      (Data.b3 d) (Data.b4 d) (Data.b6 d) (Data.factor3 d) (Data.factor4 d))
    (globalInitialTensorChart hπ data K j hj)

/-- Orienting the exterior discards neither the full incidence line nor the infinity chart. -/
theorem initialOrientedToGlobal_range (hdepth : 0 < depth) :
    Set.range (initialOrientedToGlobal hπ data D j hj hstart hk hdepth) =
      Set.range (initialGlobalIncidenceLine hπ data D j hj hstart hk) ∪
        Set.range (finiteInfinityTensorChart hπ data K j hj) := by
  rw [initialOrientedToGlobal]
  exact (initialComponent_iso_comp_range
    (initialExteriorOrientedIso hπ data D j hj hstart hk hdepth).symm
      (initialExteriorToGlobal hπ data D j hj hstart hk)).trans
        (initialExteriorToGlobal_range hπ data D j hj hstart hk)

end FLT.Mazur.WeierstrassDividedDepth
