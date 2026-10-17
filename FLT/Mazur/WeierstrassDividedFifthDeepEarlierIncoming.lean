/-
Copyright (c) 2026 krandder. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: krandder
-/
module

public import FLT.Mazur.WeierstrassDividedFifthDeepUnchanged
public import FLT.Mazur.WeierstrassDividedFifthDeepSixthOrder

/-!
# The next geometric compensation of the next earlier fifth factor

The next earlier full node supplies both punctures. Its opposite compensation
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
local notation "F" => arithmeticFifthDeepEarlierIntegralField hπ data H j hj u hu
local notation "s" => arithmeticFifthDeepEarlierSmoothing hπ data H j hj u hu m
local notation "C" => arithmeticFifthDeepEarlierIso hπ data H j hj u hu m

/-- The complete opposite substitution in the next retained incoming coordinate. -/
def arithmeticFifthDeepEarlierIncomingIso (b : Bool) : branchTorus Q ≅ branchTorus Q :=
  edgeInversion Q ≪≫ punctureSpecIso
    (correctionPunctureFactor R π m τ (F b) false) ≪≫ (edgeInversion Q).symm

/-- The full incoming square keeps the earlier node's new smoothing. -/
@[reassoc] theorem arithmeticFifthDeepEarlierIso_incoming (b : Bool) :
    precedingBranch Q τ ≫ (C b).hom =
      (arithmeticFifthDeepEarlierIncomingIso hπ data H j hj u hu m b).hom ≫
        precedingBranch Q (s b) := by
  have h := arithmeticFifthDeepEarlierIso_puncture hπ data H j hj u hu m b false
  simp only [punctureOpen_false] at h
  simp only [arithmeticFifthDeepEarlierIncomingIso, Iso.trans_hom, Iso.symm_hom,
    precedingBranch, Category.assoc, Iso.inv_hom_id_assoc]
  rw [h]

/-- The full algebraic reciprocal error realizes the actual geometric compensation. -/
theorem arithmeticFifthDeepEarlierIncomingEquiv_spec (b : Bool) :
    punctureSpecIso (arithmeticFifthDeepEarlierIncomingEquiv hπ data H j hj u hu m b) =
      arithmeticFifthDeepEarlierIncomingIso hπ data H j hj u hu m b := by
  simp only [arithmeticFifthDeepEarlierIncomingEquiv, arithmeticFifthDeepEarlierOppositeEquiv,
    punctureSpecIso_trans, punctureSpecIso_invert, arithmeticFifthDeepEarlierIncomingIso]
  rfl

omit m in
/-- The complete next incoming compensation is identity at the fifth layer. -/
theorem arithmeticFifthDeepEarlierIncomingIso_fifth (b : Bool) :
    arithmeticFifthDeepEarlierIncomingIso hπ data H j hj u hu 5 b = Iso.refl _ := by
  rw [← arithmeticFifthDeepEarlierIncomingEquiv_spec, arithmeticFifthDeepEarlierIncomingEquiv_fifth,
    punctureSpecIso_refl]
  rfl

variable [IsBezout R] (hj₄ : 4 ≤ j) (a : ℕ) (ha : a + 4 = j)
local notation "D" => arithmeticFifthDeepEarlierIdentification hπ data H m j hj u hu a ha
local notation "ι" => arithmeticFifthDeepAtlasChart hπ data H m j hj u hu hj₄
local notation "χ" => changedArithmeticAtlasChart hπ data H m j hj u hu
local notation "O" => twistedRetainedOrientation data H m

/-- The next full incoming compensation belongs to the actual installed earlier chart. -/
@[reassoc] theorem arithmeticFifthDeepEarlier_incoming (b : Bool) :
    precedingBranch Q τ ≫ (O b).hom ≫ χ (.retained ⟨a, by omega⟩ b) =
      (arithmeticFifthDeepEarlierIncomingIso hπ data H j hj u hu m b).hom ≫
        precedingBranch Q (s b) ≫ (D b).hom ≫ ι (.retained ⟨a, by omega⟩ b) := by
  rw [← arithmeticFifthDeepEarlier_original_chart hπ data H m j hj u hu hj₄ a ha b]
  rw [← Category.assoc _ (C b).hom, arithmeticFifthDeepEarlierIso_incoming, Category.assoc]

end FLT.Mazur.WeierstrassDividedDepth
