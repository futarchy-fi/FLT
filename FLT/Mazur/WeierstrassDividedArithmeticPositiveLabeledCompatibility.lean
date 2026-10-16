/-
Copyright (c) 2026 krandder. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: krandder
-/
module

public import FLT.Mazur.WeierstrassDividedArithmeticPositiveBoundaryCompatibility
public import FLT.Mazur.WeierstrassDividedArithmeticCoefficientInfinity
public import FLT.Mazur.WeierstrassDividedArithmeticInitialTriangleCompatibility

/-!
# Complete positive-retention cyclic compatibility on the original arithmetic model

Infinity, first, consecutive and terminal standard edge equations characterize
all ordered chart pairs, with full functions, both labels and exact depth indices.
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
  (H : ArithmeticAtlasCoefficients data) (m j : ℕ) (hj : j + 1 ≤ n)
local notation "c" => arithmeticLabeledAtlasMap hπ data H m (j + 1) hj
variable {Y : Scheme.{0}}
  (f : ∀ i, arithmeticLabeledAtlasObject hπ data H m (j + 1) hj i ⟶ Y)
local notation "C" => fun (i k : ArithmeticChartLabel (j + 1)) =>
  pullback.fst (c i) (c k) ≫ f i = pullback.snd (c i) (c k) ≫ f k

/-- The explicit cyclic edge equations imply every full labeled fiber-product equation. -/
theorem arithmeticPositiveLabeled_compatible
    (hInf : arithmeticInitialInfinityCompatible hπ data H m (j + 1) hj f)
    (hI : arithmeticPositiveInitialCompatible hπ data H m j hj f)
    (hA : arithmeticPositiveAdjacentCompatible hπ data H m j hj f)
    (hT : arithmeticPositiveTerminalCompatible hπ data H m j hj f) : ∀ i k, C i k := by
  have hd (i) : C i i :=
    congrArg (fun t => t ≫ f i) ((cancel_mono (c i)).mp pullback.condition)
  have hf (i k) : C i k → C k i :=
    TernaryOpenDescent.flip_compatible (c i) (c k) (f i) (f k)
  have hti : C .terminal .infinity :=
    TernaryOpenDescent.disjoint_compatible _ _ _ _
      (arithmeticLabeledAtlas_terminal_infinity_disjoint_of_coefficients
        hπ data H m (j + 1) hj)
  have hri (a : Fin (j + 1)) (b : Bool) : C (.retained a b) .infinity :=
    TernaryOpenDescent.disjoint_compatible _ _ _ _
      (arithmeticLabeledAtlas_retained_infinity_disjoint_of_coefficients
        hπ data H m (j + 1) hj a b)
  have hit (b : Bool) : C (.initial b) .terminal :=
    TernaryOpenDescent.disjoint_compatible _ _ _ _
      (arithmeticLabeledAtlas_initial_terminal_disjoint
        hπ data H m (j + 1) hj (Nat.zero_lt_succ j) b)
  have hi := (arithmeticInitialInfinity_compatible_iff hπ data H m (j + 1) hj f).mp hInf
  have hii := arithmeticInitialInfinity_initial_compatible hπ data H m (j + 1) hj f hInf
  have hbi (b : Bool) : C .infinity (.initial b) := by
    cases b
    · exact hi.1
    · exact hi.2
  have hbb (b d : Bool) : C (.initial b) (.initial d) := by
    cases b <;> cases d
    · exact hd _
    · exact hii
    · exact hf _ _ hii
    · exact hd _
  intro i k
  cases i with
  | infinity =>
    cases k with
    | infinity => exact hd _
    | terminal => exact hf _ _ hti
    | initial b => exact hbi b
    | retained a b => exact hf _ _ (hri a b)
  | terminal =>
    cases k with
    | infinity => exact hti
    | terminal => exact hd _
    | initial b => exact hf _ _ (hit b)
    | retained a b =>
      exact arithmeticPositive_terminal_retained_compatible hπ data H m j hj f hT a b
  | initial b =>
    cases k with
    | infinity => exact hf _ _ (hbi b)
    | terminal => exact hit b
    | initial d => exact hbb b d
    | retained a d =>
      exact arithmeticPositive_initial_retained_compatible hπ data H m j hj f hI a b d
  | retained a b =>
    cases k with
    | infinity => exact hri a b
    | terminal =>
      exact hf _ _
        (arithmeticPositive_terminal_retained_compatible hπ data H m j hj f hT a b)
    | initial d =>
      exact hf _ _
        (arithmeticPositive_initial_retained_compatible hπ data H m j hj f hI a d b)
    | retained e d =>
      exact arithmeticPositive_retained_compatible hπ data H m j hj f hA a e b d

/-- Full positive-retention compatibility is exactly the original cyclic edge conditions. -/
theorem arithmeticPositiveLabeled_compatible_iff :
    (∀ i k, C i k) ↔
      arithmeticInitialInfinityCompatible hπ data H m (j + 1) hj f ∧
      arithmeticPositiveInitialCompatible hπ data H m j hj f ∧
      arithmeticPositiveAdjacentCompatible hπ data H m j hj f ∧
      arithmeticPositiveTerminalCompatible hπ data H m j hj f := by
  constructor
  · intro h
    refine ⟨?_, ?_, ?_, ?_⟩
    · exact (arithmeticInitialInfinity_compatible_iff hπ data H m (j + 1) hj f).mpr
        ⟨h _ _, h _ _⟩
    · exact (arithmeticPositiveInitial_compatible_iff hπ data H m j hj f).mpr fun _ => h _ _
    · exact (arithmeticPositiveAdjacent_compatible_iff hπ data H m j hj f).mpr
        fun _ _ _ => h _ _
    · exact (arithmeticPositiveTerminal_compatible_iff hπ data H m j hj f).mpr fun _ => h _ _
  · rintro ⟨hInf, hI, hA, hT⟩
    exact arithmeticPositiveLabeled_compatible hπ data H m j hj f hInf hI hA hT

end FLT.Mazur.WeierstrassDividedDepth
