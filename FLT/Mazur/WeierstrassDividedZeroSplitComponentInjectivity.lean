/-
Copyright (c) 2026 krandder. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: krandder
-/
module

public import FLT.Mazur.WeierstrassDividedAdjacentComponentInjectivity
public import FLT.Mazur.WeierstrassDividedTerminalComponentInjectivity
public import FLT.Mazur.WeierstrassDividedZeroSplitCycle

/-!
# Injectivity of every actual split-cycle component

Pointwise injectivity survives stage transport, chain indexing and endpoint reversal.
-/

@[expose] public noncomputable section
open AlgebraicGeometry CategoryTheory IsLocalRing
namespace FLT.Mazur.WeierstrassDividedDepth
open WeierstrassModificationX
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
universe u
/-- Equality transport preserves injectivity without reducing the target scheme model. -/
theorem componentPoint_injective_eqToHom {A X Y : Scheme.{u}}
    (f : A ⟶ X) (he : X = Y) (hf : Function.Injective f) :
    Function.Injective (f ≫ eqToHom he) := by
  subst Y
  simpa only [eqToHom_refl, Category.comp_id] using hf

variable {R : Type u} [CommRing R] [IsDomain R] [IsBezout R] [IsLocalRing R]
  {W : WeierstrassCurve R} {π : R} (hπ : π ≠ 0) {start n depth : ℕ}
  (data : (i : Fin (n + 1)) → Data W π (start + i.val))
  (D : SplitNodeDepth W π depth)
local notation "K" => ResidueField R

/-- Every original ordered adjacent component is pointwise injective. -/
theorem orderedAdjacentComponent_point_injective (j : ℕ) (hj : j + 1 ≤ n)
    (hk : 2 * (start + j + 1) ≤ depth) (hjNext : j + 2 ≤ n)
    (hkNext : 2 * (start + (j + 1) + 1) ≤ depth)
    (r : ℕ) (hr : j + 2 + r ≤ n) (i : Fin 2) :
    Function.Injective (orderedAdjacentComponent hπ data D j hj hk hjNext hkNext r hr i) := by
  by_cases h : 0 < start + j
  · rw [orderedAdjacentComponent_positive hπ data D j hj hk hjNext hkNext r hr h]
    fin_cases i
    · exact adjacentRetainedFirstComponent_point_injective
        hπ data D j hj hk hjNext hkNext r hr h
    · exact adjacentRetainedSecondComponent_point_injective
        hπ data D j hj hk hjNext hkNext r hr h
  · rw [orderedAdjacentComponent_zero_depth hπ data D j hj hk hjNext hkNext r hr (by omega)]
    fin_cases i
    · exact adjacentZeroFirstComponent_point_injective
        hπ data D j hj hk hjNext hkNext r hr (by omega)
    · exact adjacentZeroSecondComponent_point_injective
        hπ data D j hj hk hjNext hkNext r hr (by omega)

variable (s : ℕ) (hs : s + 1 ≤ n) (hk : 2 * (start + s + 1) ≤ depth)

/-- Transporting to a fixed stage preserves pointwise injectivity. -/
theorem finalAdjacentComponent_point_injective (j : Fin s) (i : Fin 2) :
    Function.Injective (finalAdjacentComponent hπ data D s hs hk j i) := by
  unfold finalAdjacentComponent
  apply componentPoint_injective_eqToHom
  exact orderedAdjacentComponent_point_injective hπ data D _ _ _ _ _ _ _ i

variable (hp : 2 * (start + s + 1) < depth)

/-- Each whole terminal component is pointwise injective, including at scale one. -/
theorem finalTerminalComponent_point_injective (i : Fin 2) :
    Function.Injective (finalTerminalComponent hπ data D s hs hk hp i) := by
  by_cases h : 0 < start + s
  · rw [finalTerminalComponent_positive hπ data D s hs hk hp h]
    fin_cases i
    · exact terminalFirstComponent_point_injective hπ data D s hs hk hp h
    · exact terminalSecondComponent_point_injective hπ data D s hs hk hp h
  · rw [finalTerminalComponent_zero_depth hπ data D s hs hk hp (by omega)]
    fin_cases i
    · exact terminalZeroFirstComponent_point_injective hπ data D s hs hk hp (by omega)
    · exact terminalZeroSecondComponent_point_injective hπ data D s hs hk hp (by omega)

/-- Every full branch-chain component identifies no extra points. -/
theorem finalBranchComponent_point_injective (j : Fin (s + 1)) (i : Fin 2) :
    Function.Injective (finalBranchComponent hπ data D s hs hk hp j i).left := by
  by_cases h : j.val < s
  · rw [finalBranchComponent, dite_eq_left h]
    exact finalAdjacentComponent_point_injective hπ data D s hs hk ⟨j.val, h⟩ i
  · rw [finalBranchComponent, dite_eq_right h]
    exact finalTerminalComponent_point_injective hπ data D s hs hk hp i

variable (hstart : start = 0)

/-- The actual exterior remains injective after final-stage transport. -/
theorem finalZeroExteriorComponent_point_injective :
    Function.Injective (finalZeroExteriorComponent hπ data D s hs hstart hk) := by
  unfold finalZeroExteriorComponent
  apply componentPoint_injective_eqToHom
  exact zeroRetainedOrientedToGlobal_injective hπ data D _ _ _ _ _ _

/-- Every actual cyclic component is pointwise injective in its original orientation. -/
theorem zeroSplitCycleComponent_point_injective (i : Fin (2 * s + 3)) :
    Function.Injective (zeroSplitCycleComponent hπ data D s hs hstart hk hp i).left := by
  by_cases hi : i.val = 0
  · rw [zeroSplitCycleComponent, ite_eq_left hi]
    exact finalZeroExteriorComponent_point_injective hπ data D s hs hk hstart
  · by_cases h : i.val ≤ s + 1
    · rw [zeroSplitCycleComponent, ite_eq_right hi, dite_eq_left h]
      exact (finalBranchComponent_point_injective hπ data D s hs hk hp _ 0).comp
        (ProjectiveLine.endpointReversalIso K).hom.homeomorph.injective
    · rw [zeroSplitCycleComponent, ite_eq_right hi, dite_eq_right h]
      exact finalBranchComponent_point_injective hπ data D s hs hk hp _ 1

end FLT.Mazur.WeierstrassDividedDepth
