/-
Copyright (c) 2026 krandder. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: krandder
-/
module

public import FLT.Mazur.PolygonArithmeticSimultaneousIteration
public import FLT.Mazur.WeierstrassDividedZeroFifthResidualRestriction
public import FLT.Mazur.WeierstrassDividedZeroFifthAnnihilation

/-!
# Finite simultaneous correction states from the actual fifth depth-zero system

The seed is the constructed fifth system, including its accumulated last and
terminal drifts. Arbitrarily many further simultaneous corrections are selected
from its actual errors. This algebraic induction does not yet install the
arbitrary finite atlas or identify the downstream global target.
-/

@[expose] public noncomputable section
open scoped LaurentPolynomial
namespace FLT.Mazur.WeierstrassDividedDepth
open PolygonArithmeticStages PolygonArithmeticSimultaneous WeierstrassModificationX
set_option backward.isDefEq.respectTransparency false
attribute [local irreducible] arithmeticZeroFifthInitialEquiv arithmeticZeroFifthClosingEquiv
variable {R : Type} [CommRing R] [IsDomain R] {W : WeierstrassCurve R} {π : R}
  (hπ : π ≠ 0) {n : ℕ} (data : (i : Fin (n + 1)) → Data W π (1 + i.val))
  (H : ArithmeticAtlasCoefficients data) (j : ℕ) (hj : j + 1 ≤ n)
  (u : Rˣ) (hu : (data ⟨j + 1, Nat.lt_succ_of_le hj⟩).b6 = π * ↑u)
local notation "B" => fun m ↦ arithmeticInitialBaseEquiv data H m j hj

/-- The concrete fifth system supplies the raw initial, last and terminal parameters. -/
def arithmeticZeroFifthState : State R π where
  initial := arithmeticZeroFifthInitialSmoothing hπ data H j hj u hu
  last := arithmeticZeroFifthLastSmoothing hπ data H j hj u hu
  terminal := arithmeticZeroFifthTerminalSmoothing hπ data H j hj u hu
  initialEquiv := arithmeticZeroFifthInitialEquiv hπ data H j hj u hu
  closingEquiv := arithmeticZeroFifthClosingEquiv hπ data H j hj u hu

local notation "S" => arithmeticZeroFifthState hπ data H j hj u hu

/-- The seed retains all actual fifth coefficient squares. -/
theorem arithmeticZeroFifthState_compatible : (S).Compatible :=
  ⟨arithmeticZeroFifthInitialSmoothing_restriction hπ data H j hj u hu,
    arithmeticZeroFifthLastSmoothing_restriction hπ data H j hj u hu,
    arithmeticZeroFifthTerminalSmoothing_restriction hπ data H j hj u hu,
    (fun b m ↦ arithmeticZeroFifthInitialEquiv_restriction hπ data H j hj u hu m b),
    fun b m ↦ arithmeticZeroFifthClosingEquiv_restriction hπ data H j hj u hu m b⟩

/-- The full fifth smoothings retain the top-power annihilators of the fourth inputs. -/
theorem arithmeticZeroFifthState_annihilated : (S).Annihilated := by
  refine ⟨?_, ?_, ?_⟩
  · intro m b
    apply correctionSmoothing_annihilated
    exact arithmeticZeroFifthInitialInput_annihilated hπ data H j hj u hu m b
  · intro m b
    apply twoBranchCorrectionSmoothing_annihilated
    exact arithmeticZeroFifthLastInput_annihilated hπ data H j hj u hu m b
  · intro m
    apply twoBranchCorrectionRebasedSmoothing_annihilated
    exact arithmeticZeroFifthTerminalInput_annihilated hπ data H j hj u hu m

/-- Both seed edges are normalized by the proved fifth cancellations. -/
theorem arithmeticZeroFifthState_normalized : (S).Normalized B 5 :=
  ⟨arithmeticZeroFifthInitialEquiv_fifth hπ data H j hj u hu,
    arithmeticZeroFifthClosingEquiv_fifth hπ data H j hj u hu⟩

local notation "hS" => arithmeticZeroFifthState_compatible hπ data H j hj u hu
local notation "ha" => arithmeticZeroFifthState_annihilated hπ data H j hj u hu
local notation "hr" => arithmeticZeroFifthState_normalized hπ data H j hj u hu
local notation "hB" => arithmeticInitialBaseEquiv_restriction data H
local notation "hb" => arithmeticInitialBaseEquiv_symm_sub_mem data H

/-- Construct any finite number of further full changing-smoothing corrections. -/
def arithmeticZeroFiniteState (k : ℕ) : State R π :=
  (S).iterate B (fun m ↦ hB m j hj) (fun m ↦ hb m j hj) hS ha 5 hr k

/-- All constructed finite states retain the original quotient squares. -/
theorem arithmeticZeroFiniteState_compatible (k : ℕ) :
    (arithmeticZeroFiniteState hπ data H j hj u hu k).Compatible :=
  (S).iterate_compatible B (fun m ↦ hB m j hj) (fun m ↦ hb m j hj) hS ha 5 hr k

/-- Every accumulated finite drift preserves the actual top-power annihilator. -/
theorem arithmeticZeroFiniteState_annihilated (k : ℕ) :
    (arithmeticZeroFiniteState hπ data H j hj u hu k).Annihilated :=
  (S).iterate_annihilated B (fun m ↦ hB m j hj) (fun m ↦ hb m j hj) hS ha 5 hr k

/-- Both full residuals are simultaneously normalized at every layer from five onward. -/
theorem arithmeticZeroFiniteState_normalized (k : ℕ) :
    (arithmeticZeroFiniteState hπ data H j hj u hu k).Normalized B (5 + k) :=
  (S).iterate_normalized B (fun m ↦ hB m j hj) (fun m ↦ hb m j hj) hS ha 5 hr k

end FLT.Mazur.WeierstrassDividedDepth
