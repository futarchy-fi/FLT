/-
Copyright (c) 2026 krandder. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: krandder
-/
module

public import FLT.Mazur.WeierstrassDividedFourthOuterPreceding
public import FLT.Mazur.WeierstrassDividedFourthOuterAtlasClosing
public import FLT.Mazur.WeierstrassDividedFifthDeepInputIdentification

/-!
# Fourth inputs at the depth-three boundary

The generic paired factors already have their actual fourth inputs at depth
three. The depth-four bound is unnecessary for these three identifications.
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

/-- Each actual fourth chart is the complete input of its selected fifth paired factor. -/
def arithmeticFifthFartherInputIdentification (hj₃ : 3 ≤ j) (v : FifthDeepNode)
    (a : ℕ) (ha : a + fifthDeepOffset v = j) (b : Bool) :
    PolygonSmoothing.chart Q (arithmeticFifthDeepInput hπ data H j hj u hu v m b) ≅
      A (.retained ⟨a, by cases v <;> simp_all [fifthDeepOffset] <;> omega⟩ b) := by
  cases v
  · exact arithmeticFourthOuterPrecedingIdentification hπ data H m j hj u hu a ha (by omega) b
  · exact arithmeticFourthOuterIdentification hπ data H m j hj u hu a ha b
  · exact arithmeticFourthFartherIdentification hπ data H m j hj u hu a ha b

end FLT.Mazur.WeierstrassDividedDepth
