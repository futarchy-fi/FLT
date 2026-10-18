/-
Copyright (c) 2026 krandder. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: krandder
-/
module

public import FLT.Mazur.PolygonArithmeticRetainedChainDiagonalFactors
public import FLT.Mazur.PolygonArithmeticRetainedChainFiniteRestriction
public import FLT.Mazur.WeierstrassDividedTwoFiniteNodes

/-!
# Actual coefficient squares for the finite depth-two factors

Specialize the constructed finite factors to the proved fifth seed. Each
comparison retains its exact source and target smoothing and both punctures.
-/

@[expose] public noncomputable section
open scoped LaurentPolynomial
namespace FLT.Mazur.WeierstrassDividedDepth
open PolygonArithmeticStages PolygonArithmeticRetainedChain PolygonSmoothing
open WeierstrassModificationX
set_option backward.isDefEq.respectTransparency false
variable {R : Type} [CommRing R] [IsDomain R] {W : WeierstrassCurve R} {π : R}
  (hπ : π ≠ 0) {n : ℕ} (data : (i : Fin (n + 1)) → Data W π (1 + i.val))
  (H : ArithmeticAtlasCoefficients data) (hj : 3 ≤ n)
  (u : Rˣ) (hu : (data ⟨3, Nat.lt_succ_of_le hj⟩).b6 = π * ↑u)
local notation "B" => fun m ↦ arithmeticInitialBaseEquiv data H m 2 hj
local notation "S" => arithmeticTwoSeedState hπ data H hj u hu
local notation "hS" => arithmeticTwoSeedState_compatible hπ data H hj u hu
local notation "ha" => arithmeticTwoSeedState_annihilated hπ data H hj u hu
local notation "hr" => arithmeticTwoSeedState_normalized hπ data H hj u hu
local notation "hB" => fun m ↦ arithmeticInitialBaseEquiv_restriction data H m 2 hj
local notation "hb" => fun m ↦ arithmeticInitialBaseEquiv_symm_sub_mem data H m 2 hj
local notation "I" => arithmeticTwoFiniteState hπ data H hj u hu
variable (k m : ℕ)
local notation "Q" => Quotient R π m

local notation "f" => AlgHom.toRingHom (restriction R π m)
local notation "hI" => arithmeticTwoFiniteState_compatible hπ data H hj u hu k

/-- The full finite initial factor preserves the original smoothing coefficient maps. -/
theorem arithmeticTwoFiniteInitialFactor_restriction (b : Bool) :
    (ringMap f ((S).initial (m + 1) b) ((S).initial m b) ((hS).1 m b)).comp
      (arithmeticTwoFiniteInitialFactor hπ data H hj u hu k (m + 1) b).toRingHom =
    (arithmeticTwoFiniteInitialFactor hπ data H hj u hu k m b).toRingHom.comp
      (ringMap f ((I k).initial (m + 1) b) ((I k).initial m b) ((hI).1 m b)) :=
  (S).iterateInitialFactor_restriction B hB hb hS ha 5 hr m b k

/-- The full finite retained factor preserves the original smoothing coefficient maps. -/
theorem arithmeticTwoFiniteRetainedFactor_restriction (i : Fin 3) (b : Bool) :
    (ringMap f ((S).retained (m + 1) i b) ((S).retained m i b) ((hS).2.1 m i b)).comp
      (arithmeticTwoFiniteRetainedFactor hπ data H hj u hu k (m + 1) i b).toRingHom =
    (arithmeticTwoFiniteRetainedFactor hπ data H hj u hu k m i b).toRingHom.comp
      (ringMap f ((I k).retained (m + 1) i b) ((I k).retained m i b) ((hI).2.1 m i b)) :=
  (S).iterateRetainedFactor_restriction B hB hb hS ha 5 hr m i b k

/-- The common terminal square retains all accumulated inverse smoothing drift. -/
theorem arithmeticTwoFiniteTerminalFactor_restriction :
    (ringMap f ((I k).terminal (m + 1)) ((I k).terminal m) ((hI).2.2.1 m)).comp
      (arithmeticTwoFiniteTerminalFactor hπ data H hj u hu k (m + 1)).toRingHom =
    (arithmeticTwoFiniteTerminalFactor hπ data H hj u hu k m).toRingHom.comp
      (ringMap f ((S).terminal (m + 1)) ((S).terminal m) ((hS).2.2.1 m)) :=
  (S).iterateTerminalFactor_restriction B hB hb hS ha 5 hr m k

end FLT.Mazur.WeierstrassDividedDepth

/-!
# Actual coefficient squares for the diagonal depth-two factors

Specialize the constructed diagonal factors to the proved fifth seed. Each
comparison retains its exact source and target smoothing and both punctures.
-/

@[expose] public noncomputable section
open scoped LaurentPolynomial
namespace FLT.Mazur.WeierstrassDividedDepth
open PolygonArithmeticStages PolygonArithmeticRetainedChain PolygonSmoothing
open WeierstrassModificationX
set_option backward.isDefEq.respectTransparency false
variable {R : Type} [CommRing R] [IsDomain R] {W : WeierstrassCurve R} {π : R}
  (hπ : π ≠ 0) {n : ℕ} (data : (i : Fin (n + 1)) → Data W π (1 + i.val))
  (H : ArithmeticAtlasCoefficients data) (hj : 3 ≤ n)
  (u : Rˣ) (hu : (data ⟨3, Nat.lt_succ_of_le hj⟩).b6 = π * ↑u)
local notation "B" => fun m ↦ arithmeticInitialBaseEquiv data H m 2 hj
local notation "S" => arithmeticTwoSeedState hπ data H hj u hu
local notation "hS" => arithmeticTwoSeedState_compatible hπ data H hj u hu
local notation "ha" => arithmeticTwoSeedState_annihilated hπ data H hj u hu
local notation "hr" => arithmeticTwoSeedState_normalized hπ data H hj u hu
local notation "hB" => fun m ↦ arithmeticInitialBaseEquiv_restriction data H m 2 hj
local notation "hb" => fun m ↦ arithmeticInitialBaseEquiv_symm_sub_mem data H m 2 hj
local notation "I" => arithmeticTwoFiniteState hπ data H hj u hu
variable (m : ℕ)
local notation "Q" => Quotient R π m

local notation "f" => AlgHom.toRingHom (restriction R π m)
local notation "D" => arithmeticTwoDiagonalState hπ data H hj u hu
local notation "hI" => arithmeticTwoDiagonalState_compatible hπ data H hj u hu

/-- The full diagonal initial factor preserves the original smoothing coefficient maps. -/
theorem arithmeticTwoDiagonalInitialFactor_restriction (b : Bool) :
    (ringMap f ((S).initial (m + 1) b) ((S).initial m b) ((hS).1 m b)).comp
      (arithmeticTwoFiniteInitialFactor hπ data H hj u hu (m + 1) (m + 1) b).toRingHom =
    (arithmeticTwoFiniteInitialFactor hπ data H hj u hu m m b).toRingHom.comp
      (ringMap f ((D).initial (m + 1) b) ((D).initial m b) ((hI).1 m b)) :=
  (S).diagonalInitialFactor_restriction B hB hb hS ha 5 hr m b

/-- The full diagonal retained factor preserves the original smoothing coefficient maps. -/
theorem arithmeticTwoDiagonalRetainedFactor_restriction (i : Fin 3) (b : Bool) :
    (ringMap f ((S).retained (m + 1) i b) ((S).retained m i b) ((hS).2.1 m i b)).comp
      (arithmeticTwoFiniteRetainedFactor hπ data H hj u hu (m + 1) (m + 1) i b).toRingHom =
    (arithmeticTwoFiniteRetainedFactor hπ data H hj u hu m m i b).toRingHom.comp
      (ringMap f ((D).retained (m + 1) i b) ((D).retained m i b) ((hI).2.1 m i b)) :=
  (S).diagonalRetainedFactor_restriction B hB hb hS ha 5 hr m i b

/-- The common terminal square retains all accumulated inverse smoothing drift. -/
theorem arithmeticTwoDiagonalTerminalFactor_restriction :
    (ringMap f ((D).terminal (m + 1)) ((D).terminal m) ((hI).2.2.1 m)).comp
      (arithmeticTwoFiniteTerminalFactor hπ data H hj u hu (m + 1) (m + 1)).toRingHom =
    (arithmeticTwoFiniteTerminalFactor hπ data H hj u hu m m).toRingHom.comp
      (ringMap f ((S).terminal (m + 1)) ((S).terminal m) ((hS).2.2.1 m)) :=
  (S).diagonalTerminalFactor_restriction B hB hb hS ha 5 hr m

end FLT.Mazur.WeierstrassDividedDepth
