/-
Copyright (c) 2026 krandder. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: krandder
-/
module

public import FLT.Mazur.WeierstrassDividedFourthOuterPreceding
public import FLT.Mazur.WeierstrassDividedFourthOuterAtlasClosing
public import FLT.Mazur.WeierstrassDividedFifthDeepGeometry

/-!
# Exact fourth sources for the fifth outer-chain factors

The three paired factors are identified at their actual retained labels.
The next earlier factor starts in the unchanged normalized chart orientation.
-/

@[expose] public noncomputable section
open AlgebraicGeometry CategoryTheory
namespace FLT.Mazur.WeierstrassDividedDepth
open PolygonArithmeticStages PolygonSmoothing WeierstrassModificationX
set_option backward.isDefEq.respectTransparency false
attribute [local irreducible] finiteGlobalModel finiteGlobalContraction
  arithmeticFourthPrecedingIso arithmeticFourthAtlasCorrection
  arithmeticFourthOuterAtlasChart arithmeticThirdInitialAtlasChart
variable {R : Type} [CommRing R] [IsDomain R] [IsBezout R]
  {W : WeierstrassCurve R} {π : R} (hπ : π ≠ 0) {n : ℕ}
  (data : (i : Fin (n + 1)) → Data W π (1 + i.val))
  (H : ArithmeticAtlasCoefficients data) (m j : ℕ) (hj : j + 1 ≤ n)
  (u : Rˣ) (hu : (data ⟨j + 1, Nat.lt_succ_of_le hj⟩).b6 = π * ↑u)
local notation "Q" => Quotient R π m
local notation "τ" => arithmeticInitialMobiusSmoothing W H.a1_unit (π ^ 1) π m
local notation "A" => arithmeticFourthOuterAtlasObject hπ data H m j hj u hu

/-- Distance from the last retained node for each paired correction. -/
def fifthDeepOffset : FifthDeepNode → ℕ
  | .predecessor => 1
  | .outer => 2
  | .farther => 3

/-- Each actual fourth chart is the complete input of its selected fifth paired factor. -/
def arithmeticFifthDeepInputIdentification (hj₄ : 4 ≤ j) (v : FifthDeepNode)
    (a : ℕ) (ha : a + fifthDeepOffset v = j) (b : Bool) :
    PolygonSmoothing.chart Q (arithmeticFifthDeepInput hπ data H j hj u hu v m b) ≅
      A (.retained ⟨a, by cases v <;> simp_all [fifthDeepOffset] <;> omega⟩ b) := by
  cases v
  · exact arithmeticFourthOuterPrecedingIdentification hπ data H m j hj u hu a ha (by omega) b
  · exact arithmeticFourthOuterIdentification hπ data H m j hj u hu a ha b
  · exact arithmeticFourthFartherIdentification hπ data H m j hj u hu a ha b

/-- The next earlier label still has its original normalized full node. -/
def arithmeticFifthDeepEarlierInputIdentification (a : ℕ) (ha : a + 4 = j) (b : Bool) :
    PolygonSmoothing.chart Q τ ≅ A (.retained ⟨a, by omega⟩ b) :=
  arithmeticThirdUnchangedIdentification hπ data H m j hj u hu
    ⟨a, by omega⟩ (show a + 2 < j by omega) b ≪≫
      eqToIso (by simp only [arithmeticFourthOuterAtlasObject,
        show ¬a + 2 = j by omega, show ¬a + 3 = j by omega, ↓reduceIte,
        arithmeticFourthInitialAtlasObject, show ¬(j = 1 ∧ a = 0) by omega,
        arithmeticFourthAtlasObject, show ¬a + 1 = j by omega,
        arithmeticThirdInitialAtlasObject])

end FLT.Mazur.WeierstrassDividedDepth
