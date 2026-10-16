/-
Copyright (c) 2026 krandder. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: krandder
-/
module

public import FLT.Mazur.WeierstrassDividedArithmeticCoefficientInfinity
public import FLT.Mazur.WeierstrassDividedArithmeticInitialTriangleCompatibility
public import FLT.Mazur.WeierstrassDividedArithmeticZeroTerminalCompatibility
public import FLT.Mazur.TernaryOpenDescent

/-!
# Complete compatibility in the stage-zero labeled arithmetic atlas

The two infinity equations and the two full standard terminal equations
are necessary and sufficient for every ordered pair in the original cover.
The initial-initial equation follows from the common infinity puncture.
-/

@[expose] public noncomputable section
open AlgebraicGeometry CategoryTheory Limits
namespace FLT.Mazur.WeierstrassDividedDepth
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
attribute [local irreducible] finiteGlobalModel finiteGlobalContraction
variable {R : Type} [CommRing R] [IsDomain R] [IsBezout R]
  {W : WeierstrassCurve R} {π : R} (hπ : π ≠ 0) {start n : ℕ}
  (data : (i : Fin (n + 1)) → Data W π (start + i.val))
  (H : ArithmeticAtlasCoefficients data) (m : ℕ)
local notation "c" => arithmeticLabeledAtlasMap hπ data H m 0 (Nat.zero_le n)
variable {Y : Scheme.{0}}
  (f : ∀ i, arithmeticLabeledAtlasObject hπ data H m 0 (Nat.zero_le n) i ⟶ Y)
local notation "C" => fun (i j : ArithmeticChartLabel 0) =>
  pullback.fst (c i) (c j) ≫ f i = pullback.snd (c i) (c j) ≫ f j

/-- All full fiber-product equations follow from the four original standard endpoint equations. -/
theorem arithmeticZeroLabeled_compatible
    (hI : arithmeticInitialInfinityCompatible hπ data H m 0 (Nat.zero_le n) f)
    (hT : arithmeticZeroTerminalCompatible hπ data m H f) : ∀ i j, C i j := by
  have hd (i) : C i i :=
    congrArg (fun t => t ≫ f i) ((cancel_mono (c i)).mp pullback.condition)
  have hf (i j) : C i j → C j i :=
    TernaryOpenDescent.flip_compatible (c i) (c j) (f i) (f j)
  have hti : C .terminal .infinity :=
    TernaryOpenDescent.disjoint_compatible (c .terminal) (c .infinity)
      (f .terminal) (f .infinity)
      (arithmeticLabeledAtlas_terminal_infinity_disjoint_of_coefficients
        hπ data H m 0 (Nat.zero_le n))
  have hi := (arithmeticInitialInfinity_compatible_iff
    hπ data H m 0 (Nat.zero_le n) f).mp hI
  have ht := (arithmeticZeroTerminal_compatible_iff hπ data m H f).mp hT
  have hii := arithmeticInitialInfinity_initial_compatible hπ data H m 0 (Nat.zero_le n) f hI
  have cases_zero (i : ArithmeticChartLabel 0) :
      i = .infinity ∨ i = .terminal ∨ i = .initial false ∨ i = .initial true := by
    cases i with
    | infinity => exact Or.inl rfl
    | terminal => exact Or.inr (Or.inl rfl)
    | initial b => cases b <;> simp
    | retained a _ => exact Fin.elim0 a
  intro i j
  rcases cases_zero i with rfl | rfl | rfl | rfl <;>
    rcases cases_zero j with rfl | rfl | rfl | rfl
  · exact hd _
  · exact hf _ _ hti
  · exact hi.1
  · exact hi.2
  · exact hti
  · exact hd _
  · exact ht false
  · exact ht true
  · exact hf _ _ hi.1
  · exact hf _ _ (ht false)
  · exact hd _
  · exact hii
  · exact hf _ _ hi.2
  · exact hf _ _ (ht true)
  · exact hf _ _ hii
  · exact hd _

/-- The complete original atlas compatibility criterion has exactly four standard equations. -/
theorem arithmeticZeroLabeled_compatible_iff :
    (∀ i j, C i j) ↔
      arithmeticInitialInfinityCompatible hπ data H m 0 (Nat.zero_le n) f ∧
        arithmeticZeroTerminalCompatible hπ data m H f := by
  constructor
  · intro h
    refine ⟨?_, ?_⟩
    · exact (arithmeticInitialInfinity_compatible_iff
        hπ data H m 0 (Nat.zero_le n) f).mpr ⟨h _ _, h _ _⟩
    · exact (arithmeticZeroTerminal_compatible_iff hπ data m H f).mpr fun _ => h _ _
  · rintro ⟨hI, hT⟩
    exact arithmeticZeroLabeled_compatible hπ data H m f hI hT

end FLT.Mazur.WeierstrassDividedDepth
