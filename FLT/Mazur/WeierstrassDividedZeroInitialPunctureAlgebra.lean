/-
Copyright (c) 2026 krandder. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: krandder
-/
module

public import FLT.Mazur.WeierstrassDividedZeroInitialPunctureTransport
public import FLT.Mazur.PolygonArithmeticCorrectionPunctureReduction
public import FLT.Mazur.PolygonSmoothingPunctureSpecCalculus

/-!
# The complete initial-node puncture factor on Laurent algebras

All five preliminary factors and the actual finite factor occur in reverse
algebra order. At order zero the entire accumulated factor is identity.
-/

@[expose] public noncomputable section
open scoped LaurentPolynomial
open AlgebraicGeometry CategoryTheory
namespace FLT.Mazur.WeierstrassDividedDepth
open PolygonArithmeticStages PolygonSmoothing WeierstrassModificationX
set_option backward.isDefEq.respectTransparency false
variable {R : Type} [CommRing R] [IsDomain R]
  {W : WeierstrassCurve R} {π : R} (hπ : π ≠ 0) {n : ℕ}
  (data : (i : Fin (n + 1)) → Data W π (1 + i.val))
  (H : ArithmeticAtlasCoefficients data) (m : ℕ) (hj : 1 ≤ n)
  (u : Rˣ) (hu : (data ⟨1, Nat.lt_succ_of_le hj⟩).b6 = π * ↑u)
local notation "Q" => Quotient R π m
local notation "τ" => arithmeticInitialMobiusSmoothing W H.a1_unit (π ^ 1) π m

/-- The full diagonal boundary factor includes all six accumulated substitutions. -/
def arithmeticZeroInitialTotalPunctureEquiv (b a : Bool) : Q[T;T⁻¹] ≃ₐ[Q] Q[T;T⁻¹] :=
  (arithmeticZeroFiniteInitialPunctureEquiv hπ data H 0 hj u hu m m b a).trans
    ((correctionPunctureFactor R π m (arithmeticZeroFourthInitialSmoothing hπ data H 0 hj u hu m b)
      (arithmeticZeroFifthInitialIntegralField hπ data H 0 hj u hu b) a).trans
    ((correctionPunctureFactor R π m (arithmeticZeroThirdInitialSmoothing hπ data H 0 hj u hu m b)
      (arithmeticZeroFourthInitialIntegralField hπ data H 0 hj u hu b) a).trans
    ((correctionPunctureFactor R π m (arithmeticZeroSecondInitialSmoothing hπ data H 0 hj u hu m b)
      (arithmeticZeroThirdInitialIntegralField hπ data H 0 hj u hu b) a).trans
    ((correctionPunctureFactor R π m (arithmeticZeroFirstInitialSmoothing hπ data H 0 hj u hu m b)
      (arithmeticZeroSecondInitialIntegralField hπ data H 0 hj u hu b) a).trans
    ((correctionPunctureFactor R π m τ
      (arithmeticZeroFirstInitialIntegralField hπ data H 0 hj u hu b) a))))))

/-- Spectrum recovers the exact accumulated puncture of the original whole-node map. -/
theorem arithmeticZeroInitialTotalPunctureEquiv_spec (b a : Bool) :
    punctureSpecIso (arithmeticZeroInitialTotalPunctureEquiv hπ data H m hj u hu b a) =
      arithmeticZeroFiniteInitialTotalPunctureIso hπ data H m hj u hu m b a := by
  simp only [arithmeticZeroInitialTotalPunctureEquiv, punctureSpecIso_trans,
    arithmeticZeroFiniteInitialTotalPunctureIso, arithmeticZeroFifthInitialTotalPunctureIso,
    arithmeticZeroFourthInitialTotalPunctureIso, arithmeticZeroThirdInitialTotalPunctureIso,
    arithmeticZeroSecondInitialTotalPunctureIso, arithmeticZeroFirstInitialTotalPunctureIso]

/-- No accumulated initial correction survives at arithmetic order zero. -/
theorem arithmeticZeroInitialTotalPunctureEquiv_zero (b a : Bool) :
    arithmeticZeroInitialTotalPunctureEquiv hπ data H 0 hj u hu b a = AlgEquiv.refl := by
  have hf : arithmeticZeroFiniteInitialPunctureEquiv hπ data H 0 hj u hu 0 0 b a =
      AlgEquiv.refl := rfl
  simp only [arithmeticZeroInitialTotalPunctureEquiv, hf, correctionPunctureFactor_zero]
  rfl

end FLT.Mazur.WeierstrassDividedDepth
