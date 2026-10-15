/-
Copyright (c) 2026 krandder. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: krandder
-/
module

public import FLT.Mazur.ProjectiveCycleConstantPropagation
public import FLT.Mazur.WeierstrassDividedAdjacentComponentContraction
public import FLT.Mazur.WeierstrassDividedEqualityComponentContraction
public import FLT.Mazur.WeierstrassDividedZeroEqualityCycle

/-!
# Constancy on the entire exceptional part of the even arithmetic cycle

Every adjacent component and the single equality-depth terminal component
contracts constantly, including the reversed terminal line at depth two.
-/

@[expose] public noncomputable section
open AlgebraicGeometry CategoryTheory Limits IsLocalRing
namespace FLT.Mazur.WeierstrassDividedDepth
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
attribute [local irreducible] finiteGlobalContraction finiteGlobalStructure
  finalAdjacentComponent laurentTerminalProjectiveComponent
universe u
variable {R : Type u} [CommRing R] [IsDomain R] [IsBezout R] [IsLocalRing R]
  {W : WeierstrassCurve R} {π : R} (hπ : π ≠ 0) {start n depth : ℕ}
  (data : (i : Fin (n + 1)) → Data W π (start + i.val))
  (D : SplitNodeDepth W π depth) (s : ℕ) (hs : s + 1 ≤ n)
  (hk : 2 * (start + s + 1) ≤ depth) (hp : 2 * (start + s + 1) = depth)
local notation "K" => ResidueField R
local notation "q" => Spec.map (CommRingCat.ofHom (algebraMap R K))
local notation "f" => finiteGlobalStructure hπ data (s + 1) hs
local notation "g" => pullback.snd q f ≫ finiteGlobalContraction hπ data (s + 1) hs
variable (hstart : start = 0)
local notation "Z" => zeroEqualityCycleComponent hπ data D s hs hstart hk hp

/-- The reversed first chain still has constant original cubic contraction. -/
theorem zeroEqualityCycleComponent_first_constant (j : Fin s) :
    (Z ⟨j.val + 1, by omega⟩).left ≫ g =
      ProjectiveLine.toBase K ≫ ProjectiveLine.zero K ≫
        (Z ⟨j.val + 1, by omega⟩).left ≫ g := by
  rw [zeroEqualityCycleComponent_first]
  simp only [Over.comp_left, Category.assoc]
  exact ProjectiveCycleConstantPropagation.reparam_constant K _
    (finalAdjacentComponent_contraction_constant hπ data D s hs hk j 0) _
    (ProjectiveLine.endpointReversal_toBase K)

/-- The reversed equality-depth terminal line has constant original cubic contraction. -/
theorem zeroEqualityCycleComponent_terminal_constant :
    (Z ⟨s + 1, by omega⟩).left ≫ g =
      ProjectiveLine.toBase K ≫ ProjectiveLine.zero K ≫ (Z ⟨s + 1, by omega⟩).left ≫ g := by
  rw [zeroEqualityCycleComponent_terminal]
  simp only [Over.comp_left, Category.assoc]
  exact ProjectiveCycleConstantPropagation.reparam_constant K _
    (laurentTerminalProjectiveComponent_contraction_constant hπ data D s hs hk hp) _
    (ProjectiveLine.endpointReversal_toBase K)

/-- The second chain retains its entire constant original cubic contraction. -/
theorem zeroEqualityCycleComponent_second_constant (j : Fin s) :
    (Z ⟨2 * s + 1 - j.val, by omega⟩).left ≫ g =
      ProjectiveLine.toBase K ≫ ProjectiveLine.zero K ≫
        (Z ⟨2 * s + 1 - j.val, by omega⟩).left ≫ g := by
  rw [zeroEqualityCycleComponent_second]
  exact finalAdjacentComponent_contraction_constant hπ data D s hs hk j 1

/-- Each nonexterior component in the actual even cycle has a constant cubic contraction. -/
theorem zeroEqualityCycleComponent_contraction_constant (i : Fin (2 * s + 2)) (hi : i ≠ 0) :
    (Z i).left ≫ g =
      ProjectiveLine.toBase K ≫ ProjectiveLine.zero K ≫ (Z i).left ≫ g := by
  have hi0 : i.val ≠ 0 := fun h => hi (Fin.ext h)
  by_cases h : i.val ≤ s
  · let j : Fin s := ⟨i.val - 1, by omega⟩
    have he : i = ⟨j.val + 1, by omega⟩ := Fin.ext (by dsimp [j]; omega)
    rw [he]
    exact zeroEqualityCycleComponent_first_constant hπ data D s hs hk hp hstart j
  · by_cases ht : i.val = s + 1
    · have he : i = ⟨s + 1, by omega⟩ := Fin.ext ht
      rw [he]
      exact zeroEqualityCycleComponent_terminal_constant hπ data D s hs hk hp hstart
    · let j : Fin s := ⟨2 * s + 1 - i.val, by omega⟩
      have he : i = ⟨2 * s + 1 - j.val, by omega⟩ := Fin.ext (by dsimp [j]; omega)
      rw [he]
      exact zeroEqualityCycleComponent_second_constant hπ data D s hs hk hp hstart j

end FLT.Mazur.WeierstrassDividedDepth
