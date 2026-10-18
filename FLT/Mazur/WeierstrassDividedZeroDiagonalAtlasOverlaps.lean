/-
Copyright (c) 2026 krandder. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: krandder
-/
module

public import FLT.Mazur.WeierstrassDividedZeroDiagonalAtlas
public import FLT.Mazur.WeierstrassDividedZeroFiniteAtlasInitial
public import FLT.Mazur.WeierstrassDividedZeroFiniteAtlasClosing

/-!
# Normalized overlaps in the complete diagonal atlas

At each arithmetic order, the initial edge retains its complete original
Mobius/right base and both closing branches have identity transition.
-/

@[expose] public noncomputable section
open AlgebraicGeometry CategoryTheory
namespace FLT.Mazur.WeierstrassDividedDepth
open PolygonArithmeticStages PolygonSmoothing WeierstrassModificationX
set_option backward.isDefEq.respectTransparency false
attribute [local irreducible] finiteGlobalModel finiteGlobalContraction
  arithmeticZeroFifthAtlasChart arithmeticZeroFiniteInitialIso arithmeticZeroFiniteLastIso
  arithmeticZeroFiniteTerminalIso
variable {R : Type} [CommRing R] [IsDomain R] [IsBezout R]
  {W : WeierstrassCurve R} {π : R} (hπ : π ≠ 0) {n : ℕ}
  (data : (i : Fin (n + 1)) → Data W π (1 + i.val))
  (H : ArithmeticAtlasCoefficients data) (m : ℕ) (hj : 1 ≤ n)
  (u : Rˣ) (hu : (data ⟨1, Nat.lt_succ_of_le hj⟩).b6 = π * ↑u)
local notation "Q" => Quotient R π m
local notation "ι" => arithmeticZeroDiagonalAtlasChart hπ data H m hj u hu
local notation "D" => arithmeticZeroDiagonalState hπ data H 0 hj u hu

/-- The actual diagonal initial overlap equals its full original base at every order. -/
@[reassoc] theorem arithmeticZeroDiagonalAtlas_initial_normalized (b : Bool) :
    arithmeticZeroFiniteInitialPuncture hπ data H m m 0 hj u hu b ≫ ι (.initial b) =
      (punctureSpecIso (arithmeticInitialBaseEquiv data H m 0 hj)).hom ≫
        rightBranchOpen Q ((D).last m b) ≫ ι (.retained ⟨0, by omega⟩ b) :=
  arithmeticZeroFiniteAtlas_initial_normalized hπ data H m m hj u hu (by omega) b

/-- Both actual diagonal closing overlaps are standard at every arithmetic order. -/
@[reassoc] theorem arithmeticZeroDiagonalAtlas_closing_normalized (b : Bool) :
    (edgeInversion Q).hom ≫ leftBranchOpen Q ((D).last m b) ≫
        ι (.retained ⟨0, by omega⟩ b) =
      punctureOpen ((D).terminal m) b ≫ ι .terminal :=
  arithmeticZeroFiniteAtlas_closing_normalized hπ data H m m hj u hu (by omega) b

end FLT.Mazur.WeierstrassDividedDepth
