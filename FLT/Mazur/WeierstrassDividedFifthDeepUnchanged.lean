/-
Copyright (c) 2026 krandder. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: krandder
-/
module

public import FLT.Mazur.WeierstrassDividedFifthDeepEndIdentification
public import FLT.Mazur.WeierstrassDividedFourthFartherAdjacent

/-!
# Unchanged labels and the next earlier fifth factor

Retained labels before the full fifth chain keep their original normalized
inclusions. The next earlier factor recovers that same original orientation.
-/

@[expose] public noncomputable section
open AlgebraicGeometry CategoryTheory
namespace FLT.Mazur.WeierstrassDividedDepth
open PolygonArithmeticStages PolygonSmoothing WeierstrassModificationX
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
attribute [local irreducible] finiteGlobalModel finiteGlobalContraction
  arithmeticFourthOuterAtlasChart arithmeticFifthDeepEarlierIso arithmeticFifthDeepAtlasChart
variable {R : Type} [CommRing R] [IsDomain R] [IsBezout R]
  {W : WeierstrassCurve R} {π : R} (hπ : π ≠ 0) {n : ℕ}
  (data : (i : Fin (n + 1)) → Data W π (1 + i.val))
  (H : ArithmeticAtlasCoefficients data) (m j : ℕ) (hj : j + 1 ≤ n)
  (u : Rˣ) (hu : (data ⟨j + 1, Nat.lt_succ_of_le hj⟩).b6 = π * ↑u) (hj₄ : 4 ≤ j)
local notation "Q" => Quotient R π m
local notation "τ" => arithmeticInitialMobiusSmoothing W H.a1_unit (π ^ 1) π m
local notation "A" => arithmeticFourthOuterAtlasObject hπ data H m j hj u hu
local notation "ι" => arithmeticFourthOuterAtlasChart hπ data H m j hj u hu
local notation "κ" => arithmeticSecondJointAtlasChart hπ data H m j hj u hu
local notation "χ" => changedArithmeticAtlasChart hπ data H m j hj u hu
local notation "O" => twistedRetainedOrientation data H m

local notation "F" => arithmeticFifthDeepAtlasObject hπ data H m j hj u hu
local notation "ω" => arithmeticFifthDeepAtlasChart hπ data H m j hj u hu hj₄

omit hj₄ in
/-- An unaffected fifth label is still its original normalized full node. -/
def arithmeticFifthDeepBeforeIdentification (a : Fin (j + 1))
    (ha : a.val + 4 < j) (b : Bool) : PolygonSmoothing.chart Q τ ≅ F (.retained a b) :=
  arithmeticFourthOuterBeforeIdentification hπ data H m j hj u hu a (by omega) b ≪≫
    eqToIso (by simp only [arithmeticFifthDeepAtlasObject,
      show ¬a.val = j by omega, show ¬a.val + 1 = j by omega,
      show ¬a.val + 2 = j by omega, show ¬a.val + 3 = j by omega,
      show ¬a.val + 4 = j by omega, ↓reduceIte])

/-- The whole unaffected fifth chart retains its original global normalized inclusion. -/
@[reassoc] theorem arithmeticFifthDeepBefore_chart (a : Fin (j + 1))
    (ha : a.val + 4 < j) (b : Bool) :
    (arithmeticFifthDeepBeforeIdentification hπ data H m j hj u hu a ha b).hom ≫
      ω (.retained a b) = χ (.retained a b) := by
  have h := arithmeticFifthDeepAtlasCorrection_chart hπ data H m j hj u hu hj₄ (.retained a b)
  have hh := congrArg (fun f ↦
    (arithmeticFourthOuterBeforeIdentification hπ data H m j hj u hu a
      (show a.val + 3 < j by omega) b).hom ≫ f) h
  rw [arithmeticFourthOuterBefore_chart] at hh
  simpa only [arithmeticFifthDeepAtlasCorrection, arithmeticFifthDeepBeforeIdentification,
    show ¬a.val = j by omega, show ¬a.val + 1 = j by omega,
    show ¬a.val + 2 = j by omega, show ¬a.val + 3 = j by omega,
    show ¬a.val + 4 = j by omega, ↓reduceDIte, Iso.trans_hom, Category.assoc] using hh

variable (a : ℕ) (ha : a + 4 = j)
local notation "D" => arithmeticFifthDeepEarlierIdentification hπ data H m j hj u hu a ha
local notation "C" => arithmeticFifthDeepEarlierIso hπ data H j hj u hu m

/-- The next earlier fifth factor recovers the full original oriented inclusion. -/
@[reassoc] theorem arithmeticFifthDeepEarlier_original_chart (b : Bool) :
    (C b).hom ≫ (D b).hom ≫ ω (.retained ⟨a, by omega⟩ b) =
      (O b).hom ≫ χ (.retained ⟨a, by omega⟩ b) := by
  rw [arithmeticFifthDeepEarlier_chart]
  exact congrArg (fun f ↦ (O b).hom ≫ f)
    (arithmeticFourthOuterBefore_chart hπ data H m j hj u hu
      ⟨a, by omega⟩ (show a + 3 < j by omega) b)

end FLT.Mazur.WeierstrassDividedDepth
