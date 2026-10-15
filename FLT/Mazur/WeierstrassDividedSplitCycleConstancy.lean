/-
Copyright (c) 2026 krandder. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: krandder
-/
module

public import FLT.Mazur.ProjectiveCycleConstantPropagation
public import FLT.Mazur.WeierstrassDividedAdjacentComponentContraction
public import FLT.Mazur.WeierstrassDividedTerminalComponentContraction
public import FLT.Mazur.WeierstrassDividedZeroSplitCycle

/-!
# Constancy on the entire exceptional part of the odd arithmetic cycle

The two complete branches include their terminal components. Reversing the
first branch in the cyclic ordering preserves its constant cubic map.
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
  (hk : 2 * (start + s + 1) ≤ depth) (hp : 2 * (start + s + 1) < depth)
local notation "K" => ResidueField R
local notation "q" => Spec.map (CommRingCat.ofHom (algebraMap R K))
local notation "f" => finiteGlobalStructure hπ data (s + 1) hs
local notation "g" => pullback.snd q f ≫ finiteGlobalContraction hπ data (s + 1) hs
local notation "C" => finalBranchComponent hπ data D s hs hk hp

/-- Every whole branch component has a constant original cubic map. -/
theorem finalBranchComponent_contraction_constant (j : Fin (s + 1)) (i : Fin 2) :
    (C j i).left ≫ g =
      ProjectiveLine.toBase K ≫ ProjectiveLine.zero K ≫ (C j i).left ≫ g := by
  by_cases h : j.val < s
  · rw [finalBranchComponent, dite_eq_left h]
    exact finalAdjacentComponent_contraction_constant hπ data D s hs hk ⟨j.val, h⟩ i
  · rw [finalBranchComponent, dite_eq_right h]
    exact finalTerminalComponent_contraction_constant hπ data D s hs hk hp i

variable (hstart : start = 0)
local notation "Z" => zeroSplitCycleComponent hπ data D s hs hstart hk hp

/-- Each nonexterior component in the actual odd cycle has a constant cubic contraction. -/
theorem zeroSplitCycleComponent_contraction_constant (i : Fin (2 * s + 3)) (hi : i ≠ 0) :
    (Z i).left ≫ g =
      ProjectiveLine.toBase K ≫ ProjectiveLine.zero K ≫ (Z i).left ≫ g := by
  have hi0 : i.val ≠ 0 := fun h => hi (Fin.ext h)
  rw [zeroSplitCycleComponent, ite_eq_right hi0]
  split_ifs with h
  · change (ProjectiveLine.endpointReversal K ≫ (C ⟨i.val - 1, by omega⟩ 0).left) ≫ g = _
    simp only [Category.assoc]
    exact ProjectiveCycleConstantPropagation.reparam_constant K _
      (finalBranchComponent_contraction_constant hπ data D s hs hk hp _ 0) _
      (ProjectiveLine.endpointReversal_toBase K)
  · exact finalBranchComponent_contraction_constant hπ data D s hs hk hp _ 1

end FLT.Mazur.WeierstrassDividedDepth
