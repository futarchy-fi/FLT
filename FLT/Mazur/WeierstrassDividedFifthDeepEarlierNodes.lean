/-
Copyright (c) 2026 krandder. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: krandder
-/
module

public import FLT.Mazur.WeierstrassDividedFifthDeepCancellation
public import FLT.Mazur.WeierstrassDividedFifthPairedCancellation
public import FLT.Mazur.PolygonArithmeticHigherPunctureIdentification

/-!
# Full fifth factor before the farther retained node

The next earlier node receives the positive part of the entire fourth farther
incoming compensation. Its other puncture is retained, including its new error.
-/

@[expose] public noncomputable section
open scoped LaurentPolynomial
namespace FLT.Mazur.WeierstrassDividedDepth
open PolygonArithmeticStages PolygonSmoothing LaurentPolynomial WeierstrassModificationX
open LaurentBoundaryVectorField LaurentBoundaryCorrectionSplit
set_option backward.isDefEq.respectTransparency false
variable {R : Type} [CommRing R] [IsDomain R] {W : WeierstrassCurve R} {π : R}
  (hπ : π ≠ 0) {n : ℕ} (data : (i : Fin (n + 1)) → Data W π (1 + i.val))
  (H : ArithmeticAtlasCoefficients data) (j : ℕ) (hj : j + 1 ≤ n)
  (u : Rˣ) (hu : (data ⟨j + 1, Nat.lt_succ_of_le hj⟩).b6 = π * ↑u)
local notation "q" => arithmeticFifthResidualIntegralField hπ data H j hj u hu

/-- The next earlier field keeps the full positive farther incoming compensation. -/
def arithmeticFifthDeepEarlierField (b : Bool) : R[T;T⁻¹] :=
  positivePart (q .fartherIncoming b)

/-- The full earlier field extends over the normalized node origin. -/
theorem arithmeticFifthDeepEarlierField_boundary (b : Bool) (d : ℤ) (hd : d ≤ 0) :
    (arithmeticFifthDeepEarlierField hπ data H j hj u hu b).coeff d = 0 := by
  change (positivePart _).coeff d = 0
  rw [positivePart_coeff, ite_eq_right (by omega)]

/-- The fixed integral lift has fifth-order weight. -/
def arithmeticFifthDeepEarlierIntegralField (b : Bool) : R[T;T⁻¹] :=
  higherCorrectionField R π 4 (arithmeticFifthDeepEarlierField hπ data H j hj u hu b)

/-- The full positive farther error is recovered under fifth-stage specialization. -/
theorem arithmeticFifthDeepEarlierField_spec (b : Bool) :
    correctionField R π 5 (arithmeticFifthDeepEarlierField hπ data H j hj u hu b) =
      positivePart (arithmeticFifthResidualField hπ data H j hj u hu .fartherIncoming b) := by
  rw [arithmeticFifthDeepEarlierField, correctionField_positive,
    arithmeticFifthResidualIntegralField_spec]

local notation "τ" => fun m ↦ arithmeticInitialMobiusSmoothing W H.a1_unit (π ^ 1) π m
local notation "A" => arithmeticFifthDeepEarlierIntegralField hπ data H j hj u hu

/-- The next earlier full node keeps its new exact smoothing. -/
def arithmeticFifthDeepEarlierSmoothing (m : ℕ) (b : Bool) : Quotient R π m :=
  correctionSmoothing R π m (τ m) (A b)

/-- The earlier correction extends across the whole previously normalized node. -/
def arithmeticFifthDeepEarlierFactor (m : ℕ) (b : Bool) :
    ChartRing (arithmeticFifthDeepEarlierSmoothing hπ data H j hj u hu m b) ≃ₐ[Quotient R π m]
      ChartRing (τ m) := correctionNodeFactor R π m (τ m) (A b)

/-- Both earlier punctures come from this one full factor, including the opposite branch. -/
theorem arithmeticFifthDeepEarlierFactor_puncture (m : ℕ) (b a : Bool) :
    (punctureLaurentMap (τ m) a).comp
        (arithmeticFifthDeepEarlierFactor hπ data H j hj u hu m b).toAlgHom =
      (correctionPunctureFactor R π m (τ m) (A b) a).toAlgHom.comp
        (punctureLaurentMap (arithmeticFifthDeepEarlierSmoothing hπ data H j hj u hu m b) a) :=
  correctionNodeFactor_puncture R π m (τ m) (A b) a

/-- The entire earlier outgoing puncture realizes its fifth positive field. -/
theorem arithmeticFifthDeepEarlierPuncture_fifth (b : Bool) :
    correctionPunctureFactor R π 5 (τ 5) (A b) true =
      LaurentSquareZeroAutomorphism.equiv (parameter R π 5 ^ 5)
        (nextCorrectionParameter_square R π 4)
        (positivePart (arithmeticFifthResidualField hπ data H j hj u hu .fartherIncoming b)) := by
  apply AlgEquiv.coe_toAlgHom_injective
  apply LaurentNilpotentReparametrization.hom_ext_positive
  change correctionPunctureFactor R π 5 _ (A b) true (LaurentPolynomial.T 1) = _
  rw [arithmeticFifthDeepEarlierIntegralField, correctionPunctureFactor_higher_coordinate]
  · rw [arithmeticFifthDeepEarlierField_spec]
    exact (LaurentSquareZeroAutomorphism.equiv_T _ _ _).symm
  · exact arithmeticFifthDeepEarlierField_boundary hπ data H j hj u hu b

/-- The opposite full compensation vanishes on the fifth layer. -/
theorem arithmeticFifthDeepEarlierPuncture_opposite_fifth (b : Bool) :
    correctionPunctureFactor R π 5 (τ 5) (A b) false = AlgEquiv.refl :=
  correctionPunctureFactor_higher_opposite R π 5 4 _
    (arithmeticTopSmoothing_annihilated data H 5) _

end FLT.Mazur.WeierstrassDividedDepth
