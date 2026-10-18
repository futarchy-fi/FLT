/-
Copyright (c) 2026 krandder. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: krandder
-/
module

public import FLT.Mazur.WeierstrassDividedZeroRetainedEdgeRestriction
public import FLT.Mazur.PolygonArithmeticCyclicState

/-!
# The concrete five-node depth-zero cyclic seed

The orientation is terminal, reflected retained, reflected initial, initial,
retained. Every full retained substitution and every actual smoothing is kept.
-/

@[expose] public noncomputable section
open scoped LaurentPolynomial
namespace FLT.Mazur.WeierstrassDividedDepth
open PolygonArithmeticStages PolygonArithmeticCyclic PolygonSmoothing
open WeierstrassModificationX LaurentPolynomial
set_option backward.isDefEq.respectTransparency false

/-- The five entire nodes after normalizing the common initial/infinity union. -/
inductive ZeroCyclicVertex
  | terminal
  | retained (branch : Bool)
  | initial (branch : Bool)
  deriving DecidableEq, Fintype

/-- Traverse the actual five nodes, reflecting both nodes on the true branch. -/
def zeroCyclicSuccessor : Equiv.Perm ZeroCyclicVertex where
  toFun
    | .terminal => .retained true
    | .retained true => .initial true
    | .initial true => .initial false
    | .initial false => .retained false
    | .retained false => .terminal
  invFun
    | .retained true => .terminal
    | .initial true => .retained true
    | .initial false => .initial true
    | .retained false => .initial false
    | .terminal => .retained false
  left_inv := by rintro (_ | (_ | _) | (_ | _)) <;> rfl
  right_inv := by rintro (_ | (_ | _) | (_ | _)) <;> rfl

variable {R : Type} [CommRing R] [IsDomain R]
  {W : WeierstrassCurve R} {π : R} (hπ : π ≠ 0) {n : ℕ}
  (data : (i : Fin (n + 1)) → Data W π (1 + i.val))
  (H : ArithmeticAtlasCoefficients data) (hj : 1 ≤ n)
  (u : Rˣ) (hu : (data ⟨1, Nat.lt_succ_of_le hj⟩).b6 = π * ↑u)
local notation "D" => arithmeticZeroDiagonalState hπ data H 0 hj u hu
local notation "hD" => arithmeticZeroDiagonalState_compatible hπ data H 0 hj u hu
local notation "ha" => arithmeticZeroDiagonalState_annihilated hπ data H 0 hj u hu
local notation "E" => fun k ↦ arithmeticZeroRetainedEdgeEquiv hπ data H k hj u hu

/-- The actual exact-twist data on all five nodes, before cyclic normalization. -/
def arithmeticZeroCyclicSeed : State R π ZeroCyclicVertex where
  parameter m
    | .terminal => (D).terminal m
    | .retained b => (D).last m b
    | .initial _ => arithmeticInitialMobiusSmoothing W H.a1_unit (π ^ 1) π m
  edge m
    | .terminal => invert
    | .retained true => (E m true).symm
    | .initial true => invert
    | .initial false => E m false
    | .retained false => invert

local notation "S" => arithmeticZeroCyclicSeed hπ data H hj u hu

/-- Every smoothing and every full edge has the original coefficient square. -/
theorem arithmeticZeroCyclicSeed_compatible [IsBezout R] : (S).Compatible := by
  constructor
  · intro m i
    cases i with
    | terminal => exact (hD).2.2.1 m
    | retained b => exact (hD).2.1 m b
    | initial b =>
      exact arithmeticInitialMobiusSmoothing_restriction W H.a1_unit (π ^ 1) π m
  · intro i m
    cases i with
    | terminal => exact punctureEquiv_invert_naturality _
    | retained b =>
      cases b
      · exact punctureEquiv_invert_naturality _
      · exact LaurentUnitSubstitutionNaturality.symm_naturality _ _ _
          (arithmeticZeroRetainedEdgeEquiv_restriction hπ data H m hj u hu true)
    | initial b =>
      cases b
      · exact arithmeticZeroRetainedEdgeEquiv_restriction hπ data H m hj u hu false
      · exact punctureEquiv_invert_naturality _

/-- The actual five smoothings satisfy the required top-power annihilator. -/
theorem arithmeticZeroCyclicSeed_annihilated : (S).Annihilated := by
  intro m i
  cases i with
  | terminal => exact (ha).2.2 m
  | retained b => exact (ha).2.1 m b
  | initial b => exact arithmeticTopSmoothing_annihilated data H m

/-- The complete concrete cyclic seed is normalized already at arithmetic order zero. -/
theorem arithmeticZeroCyclicSeed_normalized : (S).Normalized 0 := by
  rintro (_ | (_ | _) | (_ | _)) <;>
    simp only [arithmeticZeroCyclicSeed, arithmeticZeroRetainedEdgeEquiv_zero, invert_symm]

end FLT.Mazur.WeierstrassDividedDepth
