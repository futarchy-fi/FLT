/-
Copyright (c) 2026 krandder. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: krandder
-/
module

public import FLT.Mazur.WeierstrassDividedThirdSmoothingAnnihilation
public import FLT.Mazur.PolygonSmoothingPunctureIdentification

/-!
# Full square-zero identification of the third shared and predecessor factors

Each node carries both prescribed finite fields on its actual previous
smoothing. The entire lifted factor specializes to that one node automorphism.
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
local notation "Q" => Quotient R π 3
local notation "e" => parameter R π 3 ^ 3
local notation "he" => nextCorrectionParameter_square R π 2
local notation "τ" => arithmeticInitialMobiusSmoothing W H.a1_unit (π ^ 1) π 3
local notation "s" => arithmeticSecondPrecedingSmoothing hπ data H 3 j hj u hu
local notation "v" => arithmeticThirdLastField hπ data H j hj u hu
local notation "w" => arithmeticThirdPrecedingField hπ data H j hj u hu
local notation "V" => arithmeticThirdLastIntegralField hπ data H j hj u hu

/-- The two full finite third fields on each last retained node. -/
def arithmeticThirdLastLayerField (b a : Bool) : Q[T;T⁻¹] := correctionField R π 3 (v b a)

/-- The two full finite third fields on each already corrected predecessor. -/
def arithmeticThirdPrecedingLayerField (b a : Bool) : Q[T;T⁻¹] :=
  correctionField R π 3 (w b a)

local notation "p" => arithmeticThirdLastLayerField hπ data H j hj u hu
local notation "q" => arithmeticThirdPrecedingLayerField hπ data H j hj u hu

/-- The entire last-node field is positive in its own boundary coordinate. -/
theorem arithmeticThirdLastLayerField_positive (b a : Bool) : positivePart (p b a) = p b a := by
  ext d
  rw [positivePart_coeff]
  split_ifs with hd
  · rfl
  · exact (correctionField_boundary R π 3 (v b a)
      (arithmeticThirdLastField_boundary hπ data H j hj u hu b a) d (by omega)).symm

/-- The entire predecessor field is positive in its own boundary coordinate. -/
theorem arithmeticThirdPrecedingLayerField_positive (b a : Bool) :
    positivePart (q b a) = q b a := by
  ext d
  rw [positivePart_coeff]
  split_ifs with hd
  · rfl
  · exact (correctionField_boundary R π 3 (w b a)
      (arithmeticThirdPrecedingField_boundary hπ data H j hj u hu b a) d (by omega)).symm

/-- One full node automorphism realizes both last-node third fields simultaneously. -/
def arithmeticThirdLastLayerFactor (b : Bool) : ChartRing τ ≃ₐ[Q] ChartRing τ :=
  squareZeroTwoBranchFactor τ e he (arithmeticTopSmoothing_annihilated data H 3) (p b)

/-- One full predecessor automorphism retains its exact second smoothing. -/
def arithmeticThirdPrecedingLayerFactor (b : Bool) : ChartRing (s b) ≃ₐ[Q] ChartRing (s b) :=
  squareZeroTwoBranchFactor (s b) e he
    (arithmeticThirdPrecedingInput_annihilated hπ data H j hj u hu b) (q b)

/-- The whole third lift on the last node is its square-zero node factor at stage three. -/
theorem arithmeticThirdLastFactor_third (b : Bool) :
    (arithmeticThirdLastFactor hπ data H j hj u hu 3 b).toAlgHom.toRingHom =
      (arithmeticThirdLastLayerFactor hπ data H j hj u hu b).toAlgHom.toRingHom.comp
        (ringMap (RingHom.id Q) (twoBranchCorrectionSmoothing R π 3 τ (V b)) τ
          (arithmeticThirdLastSmoothing_pair hπ data H j hj u hu 3 b)) := by
  apply twoBranchCorrectionNodeFactor_higher_eq R π 3 2 he τ
    (arithmeticTopSmoothing_annihilated data H 3) (v b) (p b)
  intro a
  exact (arithmeticThirdLastLayerField_positive hπ data H j hj u hu b a).symm

/-- The whole predecessor lift is identified without discarding its previous smoothing drift. -/
theorem arithmeticThirdPrecedingFactor_third (b : Bool) :
    (arithmeticThirdPrecedingFactor hπ data H j hj u hu 3 b).toAlgHom.toRingHom =
      (arithmeticThirdPrecedingLayerFactor hπ data H j hj u hu b).toAlgHom.toRingHom.comp
        (ringMap (RingHom.id Q)
          (arithmeticThirdPrecedingSmoothing hπ data H j hj u hu 3 b) (s b)
          (arithmeticThirdPrecedingSmoothing_third hπ data H j hj u hu b)) := by
  apply twoBranchCorrectionNodeFactor_higher_eq R π 3 2 he (s b)
    (arithmeticThirdPrecedingInput_annihilated hπ data H j hj u hu b) (w b) (q b)
  intro a
  exact (arithmeticThirdPrecedingLayerField_positive hπ data H j hj u hu b a).symm

end FLT.Mazur.WeierstrassDividedDepth
