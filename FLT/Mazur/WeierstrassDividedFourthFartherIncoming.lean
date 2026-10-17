/-
Copyright (c) 2026 krandder. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: krandder
-/
module

public import FLT.Mazur.WeierstrassDividedFourthOuterIdentification
public import FLT.Mazur.WeierstrassDividedFourthFartherFifthOrder

/-!
# The next geometric compensation of the farther fourth factor

The farther full node supplies both punctures. Its opposite compensation
is compared with the original normalized chart at its installed global label.
-/

@[expose] public noncomputable section
open AlgebraicGeometry CategoryTheory
namespace FLT.Mazur.WeierstrassDividedDepth
open PolygonArithmeticStages PolygonSmoothing WeierstrassModificationX
set_option backward.isDefEq.respectTransparency false
variable {R : Type} [CommRing R] [IsDomain R] {W : WeierstrassCurve R} {π : R}
  (hπ : π ≠ 0) {n : ℕ} (data : (i : Fin (n + 1)) → Data W π (1 + i.val))
  (H : ArithmeticAtlasCoefficients data) (j : ℕ) (hj : j + 1 ≤ n)
  (u : Rˣ) (hu : (data ⟨j + 1, Nat.lt_succ_of_le hj⟩).b6 = π * ↑u)
  (m : ℕ)
local notation "Q" => Quotient R π m
local notation "τ" => arithmeticInitialMobiusSmoothing W H.a1_unit (π ^ 1) π m
local notation "F" => arithmeticFourthFartherIntegralField hπ data H j hj u hu
local notation "s" => arithmeticFourthFartherSmoothing hπ data H j hj u hu m
local notation "C" => arithmeticFourthFartherIso hπ data H j hj u hu m

/-- The complete opposite substitution in the next retained incoming coordinate. -/
def arithmeticFourthFartherIncomingIso (b : Bool) : branchTorus Q ≅ branchTorus Q :=
  edgeInversion Q ≪≫ punctureSpecIso
    (correctionPunctureFactor R π m τ (F b) false) ≪≫ (edgeInversion Q).symm

/-- The full incoming square keeps the farther node's new smoothing. -/
@[reassoc] theorem arithmeticFourthFartherIso_incoming (b : Bool) :
    precedingBranch Q τ ≫ (C b).hom =
      (arithmeticFourthFartherIncomingIso hπ data H j hj u hu m b).hom ≫
        precedingBranch Q (s b) := by
  have h := arithmeticFourthFartherIso_puncture hπ data H j hj u hu m b false
  simp only [punctureOpen_false] at h
  simp only [arithmeticFourthFartherIncomingIso, Iso.trans_hom, Iso.symm_hom,
    precedingBranch, Category.assoc, Iso.inv_hom_id_assoc]
  rw [h]

/-- The full algebraic reciprocal error realizes the actual geometric compensation. -/
theorem arithmeticFourthFartherIncomingEquiv_spec (b : Bool) :
    punctureSpecIso (arithmeticFourthFartherIncomingEquiv hπ data H j hj u hu m b) =
      arithmeticFourthFartherIncomingIso hπ data H j hj u hu m b := by
  simp only [arithmeticFourthFartherIncomingEquiv, arithmeticFourthFartherOppositeEquiv,
    punctureSpecIso_trans, punctureSpecIso_invert, arithmeticFourthFartherIncomingIso]
  rfl

omit m in
/-- The complete next incoming compensation is identity at the fourth layer. -/
theorem arithmeticFourthFartherIncomingIso_fourth (b : Bool) :
    arithmeticFourthFartherIncomingIso hπ data H j hj u hu 4 b = Iso.refl _ := by
  rw [← arithmeticFourthFartherIncomingEquiv_spec, arithmeticFourthFartherIncomingEquiv_fourth,
    punctureSpecIso_refl]
  rfl

variable [IsBezout R] (a : ℕ) (ha : a + 3 = j)
local notation "D" => arithmeticFourthFartherIdentification hπ data H m j hj u hu a ha
local notation "ι" => arithmeticFourthOuterAtlasChart hπ data H m j hj u hu
local notation "χ" => changedArithmeticAtlasChart hπ data H m j hj u hu
local notation "O" => twistedRetainedOrientation data H m

/-- The installed farther full node recovers the original oriented normalized inclusion. -/
@[reassoc] theorem arithmeticFourthFarther_original_chart (b : Bool) :
    (C b).hom ≫ (D b).hom ≫ ι (.retained ⟨a, by omega⟩ b) =
      (O b).hom ≫ χ (.retained ⟨a, by omega⟩ b) := by
  rw [arithmeticFourthFarther_chart, arithmeticThirdInitialAtlasChart_retained,
    arithmeticThirdUnchanged_chart]

/-- The next full incoming compensation belongs to the actual installed farther chart. -/
@[reassoc] theorem arithmeticFourthFarther_incoming (b : Bool) :
    precedingBranch Q τ ≫ (O b).hom ≫ χ (.retained ⟨a, by omega⟩ b) =
      (arithmeticFourthFartherIncomingIso hπ data H j hj u hu m b).hom ≫
        precedingBranch Q (s b) ≫ (D b).hom ≫ ι (.retained ⟨a, by omega⟩ b) := by
  rw [← arithmeticFourthFarther_original_chart hπ data H j hj u hu m a ha b]
  rw [← Category.assoc _ (C b).hom, arithmeticFourthFartherIso_incoming, Category.assoc]

end FLT.Mazur.WeierstrassDividedDepth
