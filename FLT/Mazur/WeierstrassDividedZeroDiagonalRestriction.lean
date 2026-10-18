/-
Copyright (c) 2026 krandder. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: krandder
-/
module

public import FLT.Mazur.PolygonArithmeticSimultaneousDiagonalFactors
public import FLT.Mazur.WeierstrassDividedZeroDiagonalState
public import FLT.Mazur.WeierstrassDividedZeroFiniteNodes

/-!
# Actual coefficient squares for the diagonal depth-zero factors

The correction count changes across each quotient. Both complete puncture
squares prove the actual node squares on the accumulated diagonal smoothings.
-/

@[expose] public noncomputable section
open scoped LaurentPolynomial
namespace FLT.Mazur.WeierstrassDividedDepth
open PolygonArithmeticStages PolygonArithmeticSimultaneous PolygonSmoothing
open WeierstrassModificationX
set_option backward.isDefEq.respectTransparency false
variable {R : Type} [CommRing R] [IsDomain R] {W : WeierstrassCurve R} {π : R}
  (hπ : π ≠ 0) {n : ℕ} (data : (i : Fin (n + 1)) → Data W π (1 + i.val))
  (H : ArithmeticAtlasCoefficients data) (j : ℕ) (hj : j + 1 ≤ n)
  (u : Rˣ) (hu : (data ⟨j + 1, Nat.lt_succ_of_le hj⟩).b6 = π * ↑u)
local notation "B" => fun m ↦ arithmeticInitialBaseEquiv data H m j hj
local notation "S" => arithmeticZeroFifthState hπ data H j hj u hu
local notation "hS" => arithmeticZeroFifthState_compatible hπ data H j hj u hu
local notation "ha" => arithmeticZeroFifthState_annihilated hπ data H j hj u hu
local notation "hr" => arithmeticZeroFifthState_normalized hπ data H j hj u hu
local notation "hB" => fun m ↦ arithmeticInitialBaseEquiv_restriction data H m j hj
local notation "hb" => fun m ↦ arithmeticInitialBaseEquiv_symm_sub_mem data H m j hj
local notation "I" => arithmeticZeroFiniteState hπ data H j hj u hu
variable (m : ℕ)
local notation "Q" => Quotient R π m

local notation "f" => AlgHom.toRingHom (restriction R π m)
local notation "D" => arithmeticZeroDiagonalState hπ data H j hj u hu
local notation "hD" => arithmeticZeroDiagonalState_compatible hπ data H j hj u hu

/-- The full finite initial factor preserves the original smoothing coefficient maps. -/
theorem arithmeticZeroDiagonalInitialFactor_restriction (b : Bool) :
    (ringMap f ((S).initial (m + 1) b) ((S).initial m b) ((hS).1 m b)).comp
      (arithmeticZeroFiniteInitialFactor hπ data H j hj u hu (m + 1) (m + 1) b).toRingHom =
    (arithmeticZeroFiniteInitialFactor hπ data H j hj u hu m m b).toRingHom.comp
      (ringMap f ((D).initial (m + 1) b) ((D).initial m b) ((hD).1 m b)) :=
  (S).diagonalInitialFactor_restriction B hB hb hS ha 5 hr m b

/-- The full finite last factor preserves the original smoothing coefficient maps. -/
theorem arithmeticZeroDiagonalLastFactor_restriction (b : Bool) :
    (ringMap f ((S).last (m + 1) b) ((S).last m b) ((hS).2.1 m b)).comp
      (arithmeticZeroFiniteLastFactor hπ data H j hj u hu (m + 1) (m + 1) b).toRingHom =
    (arithmeticZeroFiniteLastFactor hπ data H j hj u hu m m b).toRingHom.comp
      (ringMap f ((D).last (m + 1) b) ((D).last m b) ((hD).2.1 m b)) :=
  (S).diagonalLastFactor_restriction B hB hb hS ha 5 hr m b

/-- The common terminal square retains all accumulated inverse smoothing drift. -/
theorem arithmeticZeroDiagonalTerminalFactor_restriction :
    (ringMap f ((D).terminal (m + 1)) ((D).terminal m) ((hD).2.2.1 m)).comp
      (arithmeticZeroFiniteTerminalFactor hπ data H j hj u hu (m + 1) (m + 1)).toRingHom =
    (arithmeticZeroFiniteTerminalFactor hπ data H j hj u hu m m).toRingHom.comp
      (ringMap f ((S).terminal (m + 1)) ((S).terminal m) ((hS).2.2.1 m)) :=
  (S).diagonalTerminalFactor_restriction B hB hb hS ha 5 hr m

end FLT.Mazur.WeierstrassDividedDepth
