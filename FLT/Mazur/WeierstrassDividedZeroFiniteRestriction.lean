/-
Copyright (c) 2026 krandder. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: krandder
-/
module

public import FLT.Mazur.PolygonArithmeticSimultaneousFiniteRestriction
public import FLT.Mazur.WeierstrassDividedZeroFiniteNodes

/-!
# Actual coefficient squares for the finite depth-zero factors

Specialize the constructed finite factors to the proved fifth seed. Each
comparison retains its exact source and target smoothing and both punctures.
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
variable (k m : ℕ)
local notation "Q" => Quotient R π m

local notation "f" => AlgHom.toRingHom (restriction R π m)
local notation "hI" => arithmeticZeroFiniteState_compatible hπ data H j hj u hu k

/-- The full finite initial factor preserves the original smoothing coefficient maps. -/
theorem arithmeticZeroFiniteInitialFactor_restriction (b : Bool) :
    (ringMap f ((S).initial (m + 1) b) ((S).initial m b) ((hS).1 m b)).comp
      (arithmeticZeroFiniteInitialFactor hπ data H j hj u hu k (m + 1) b).toRingHom =
    (arithmeticZeroFiniteInitialFactor hπ data H j hj u hu k m b).toRingHom.comp
      (ringMap f ((I k).initial (m + 1) b) ((I k).initial m b) ((hI).1 m b)) :=
  (S).iterateInitialFactor_restriction B hB hb hS ha 5 hr m b k

/-- The full finite last factor preserves the original smoothing coefficient maps. -/
theorem arithmeticZeroFiniteLastFactor_restriction (b : Bool) :
    (ringMap f ((S).last (m + 1) b) ((S).last m b) ((hS).2.1 m b)).comp
      (arithmeticZeroFiniteLastFactor hπ data H j hj u hu k (m + 1) b).toRingHom =
    (arithmeticZeroFiniteLastFactor hπ data H j hj u hu k m b).toRingHom.comp
      (ringMap f ((I k).last (m + 1) b) ((I k).last m b) ((hI).2.1 m b)) :=
  (S).iterateLastFactor_restriction B hB hb hS ha 5 hr m b k

/-- The common terminal square retains all accumulated inverse smoothing drift. -/
theorem arithmeticZeroFiniteTerminalFactor_restriction :
    (ringMap f ((I k).terminal (m + 1)) ((I k).terminal m) ((hI).2.2.1 m)).comp
      (arithmeticZeroFiniteTerminalFactor hπ data H j hj u hu k (m + 1)).toRingHom =
    (arithmeticZeroFiniteTerminalFactor hπ data H j hj u hu k m).toRingHom.comp
      (ringMap f ((S).terminal (m + 1)) ((S).terminal m) ((hS).2.2.1 m)) :=
  (S).iterateTerminalFactor_restriction B hB hb hS ha 5 hr m k

end FLT.Mazur.WeierstrassDividedDepth
