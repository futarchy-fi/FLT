/-
Copyright (c) 2026 krandder. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: krandder
-/
module

public import FLT.LocalClassFieldTheory.PeuScalarCoordinates
public import FLT.LocalClassFieldTheory.PeuClassSubmodule

/-!
# The extended annihilator is the span of the prime annihilator

Finite coefficient coordinates reconstruct the class from included prime
classes. The reverse inclusion tests every extended unramified character.
-/

@[expose] public noncomputable section

set_option backward.isDefEq.respectTransparency false

namespace LocalClassFieldTheory

open GaloisRepresentation.Extensions

variable {G F k ι : Type*} [Group G] [TopologicalSpace G]
  [Field F] [TopologicalSpace F] [DiscreteTopology F]
  [Field k] [TopologicalSpace k] [DiscreteTopology k] [Algebra F k]
  [Fintype ι] (χ : G →* Fˣ) (b : Module.Basis ι F k)

omit [TopologicalSpace F] [DiscreteTopology F] [TopologicalSpace k] [DiscreteTopology k] in
/-- Reconstruct an extended class by including its prime coordinates. -/
theorem characterClass_reconstruct (x : LinearContinuousClass k G (CharacterModule χ k)) :
    x = ∑ i, b i • extendCharacterClass (k := k) χ (linearCharacterCoordinates χ b x i) := by
  classical
  apply linearCharacterCoordinates_injective χ b
  funext j
  change linearCharacterCoordinates χ b x j =
    linearCharacterCoordinates χ b (∑ i, b i • extendCharacterClass (k := k) χ
      (linearCharacterCoordinates χ b x i)) j
  rw [map_sum]
  simp only [Finset.sum_apply]
  simp only [coordinate_smul_extend, Module.Basis.repr_self, Finsupp.single_apply,
    ite_smul, one_smul, zero_smul, Finset.sum_ite_eq', Finset.mem_univ, ite_true]

omit [Fintype ι] in
include b in
/-- The independent annihilator commutes with finite residual-field scalar extension. -/
theorem peuClassSubmodule_eq_extendedSpan [Finite ι] (I : Subgroup G) :
    peuClassSubmodule (F := k) (M := CharacterModule χ k) I =
      Submodule.span k (extendCharacterClass (k := k) χ ''
        (peuClassSubmodule (F := F) (M := CharacterModule χ F) I : Set _)) := by
  classical
  let := Fintype.ofFinite ι
  apply le_antisymm
  · intro x hx
    have hc := (isPeuRamifiedClass_coordinates_iff χ b I x).mp hx
    rw [characterClass_reconstruct χ b x]
    exact Submodule.sum_mem _ fun i _ => Submodule.smul_mem _ _
      (Submodule.subset_span ⟨_, hc i, rfl⟩)
  · apply Submodule.span_le.mpr
    rintro _ ⟨x, hx, rfl⟩
    induction x using Quotient.inductionOn with | h c =>
      exact peuCocycle_inclusion χ b I c hx

end LocalClassFieldTheory
