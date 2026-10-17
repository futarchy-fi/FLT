/-
Copyright (c) 2026 krandder. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: krandder
-/
module

public import FLT.Mazur.WeierstrassDividedThirdEarlierGeometry
public import FLT.Mazur.WeierstrassDividedThirdPunctureIdentification

/-!
# The incoming puncture of the full earlier third correction

The opposite compensation retains its exact smoothing at every order.
Both its direct and reciprocal forms are identity on the third layer.
-/

@[expose] public noncomputable section
open AlgebraicGeometry CategoryTheory
namespace FLT.Mazur.WeierstrassDividedDepth
open PolygonArithmeticStages PolygonSmoothing WeierstrassModificationX
set_option backward.isDefEq.respectTransparency false
variable {R : Type} [CommRing R] [IsDomain R] {W : WeierstrassCurve R} {π : R}
  (hπ : π ≠ 0) {n : ℕ} (data : (i : Fin (n + 1)) → Data W π (1 + i.val))
  (H : ArithmeticAtlasCoefficients data) (m j : ℕ) (hj : j + 1 ≤ n)
  (u : Rˣ) (hu : (data ⟨j + 1, Nat.lt_succ_of_le hj⟩).b6 = π * ↑u)
local notation "Q" => Quotient R π m
local notation "τ" => arithmeticInitialMobiusSmoothing W H.a1_unit (π ^ 1) π m
local notation "O" => twistedRetainedOrientation data H m
local notation "P" => arithmeticThirdEarlierOrientedIso hπ data H m j hj u hu
local notation "s" => arithmeticThirdEarlierSmoothing hπ data H j hj u hu m
local notation "B" => fun b ↦ correctionPunctureFactor R π m τ
  (arithmeticThirdEarlierIntegralField hπ data H j hj u hu b)

/-- The opposite full substitution in the original reciprocal incoming parameter. -/
def arithmeticThirdEarlierIncomingIso (b : Bool) : branchTorus Q ≅ branchTorus Q :=
  edgeInversion Q ≪≫ punctureSpecIso (B b false) ≪≫ (edgeInversion Q).symm

/-- The full right puncture square keeps the earlier node's exact smoothing. -/
@[reassoc] theorem arithmeticThirdEarlierOrientedIso_right (b : Bool) :
    (rightBranchOpen Q τ ≫ (O b).hom) ≫ (P b).hom =
      (punctureSpecIso (B b false)).hom ≫ rightBranchOpen Q (s b) := by
  rw [Category.assoc, arithmeticThirdEarlierOrientedIso_hom]
  simpa only [punctureOpen_false] using
    arithmeticThirdEarlierIso_puncture hπ data H m j hj u hu b false

/-- The same full square in the parameter used by adjacent retained edges. -/
@[reassoc] theorem arithmeticThirdEarlierOrientedIso_incoming (b : Bool) :
    (precedingBranch Q τ ≫ (O b).hom) ≫ (P b).hom =
      (arithmeticThirdEarlierIncomingIso hπ data H m j hj u hu b).hom ≫
        precedingBranch Q (s b) := by
  simp only [arithmeticThirdEarlierIncomingIso, Iso.trans_hom, Iso.symm_hom,
    precedingBranch, Category.assoc, Iso.inv_hom_id_assoc]
  rw [← Category.assoc (rightBranchOpen Q τ), arithmeticThirdEarlierOrientedIso_right]

omit m in
/-- The entire reciprocal incoming substitution is identity on the third layer. -/
theorem arithmeticThirdEarlierIncomingIso_third (b : Bool) :
    arithmeticThirdEarlierIncomingIso hπ data H 3 j hj u hu b = Iso.refl _ := by
  simp only [arithmeticThirdEarlierIncomingIso,
    arithmeticThirdEarlierPuncture_opposite_third hπ data H j hj u hu b, punctureSpecIso_refl]
  ext
  simp only [Iso.trans_hom, Iso.refl_hom, Iso.symm_hom]
  change (edgeInversion _).hom ≫ (𝟙 _ ≫ (edgeInversion _).inv) = _
  rw [Category.id_comp, Iso.hom_inv_id]

variable [IsBezout R] (a : ℕ) (ha : a + 2 = j)
local notation "ι" => arithmeticThirdAtlasChart hπ data H m j hj u hu
local notation "χ" => changedArithmeticAtlasChart hπ data H m j hj u hu
local notation "M" => arithmeticThirdEarlierIdentification hπ data H m j hj u hu a ha

/-- The earlier full factor recovers the original normalized chart inclusion. -/
@[reassoc] theorem arithmeticThirdEarlier_original_chart (b : Bool) :
    (P b).hom ≫ (M b).hom ≫ ι (.retained ⟨a, by omega⟩ b) =
      χ (.retained ⟨a, by omega⟩ b) := by
  rw [arithmeticThirdEarlier_chart, arithmeticSecondJointEarlier_chart]

/-- The installed earlier label keeps the exact reciprocal incoming correction. -/
@[reassoc] theorem arithmeticThirdEarlier_incoming (b : Bool) :
    precedingBranch Q τ ≫ (O b).hom ≫ χ (.retained ⟨a, by omega⟩ b) =
      (arithmeticThirdEarlierIncomingIso hπ data H m j hj u hu b).hom ≫
        precedingBranch Q (s b) ≫ (M b).hom ≫ ι (.retained ⟨a, by omega⟩ b) := by
  rw [← arithmeticThirdEarlier_original_chart hπ data H m j hj u hu a ha b]
  simpa only [Category.assoc] using congrArg
    (fun f ↦ f ≫ (M b).hom ≫ ι (.retained ⟨a, by omega⟩ b))
    (arithmeticThirdEarlierOrientedIso_incoming hπ data H m j hj u hu b)

/-- The direct opposite puncture is the one used by the original initial diagram. -/
@[reassoc] theorem arithmeticThirdEarlier_right (b : Bool) :
    rightBranchOpen Q τ ≫ (O b).hom ≫ χ (.retained ⟨a, by omega⟩ b) =
      (punctureSpecIso (B b false)).hom ≫ rightBranchOpen Q (s b) ≫
        (M b).hom ≫ ι (.retained ⟨a, by omega⟩ b) := by
  rw [← arithmeticThirdEarlier_original_chart hπ data H m j hj u hu a ha b]
  simpa only [Category.assoc] using congrArg
    (fun f ↦ f ≫ (M b).hom ≫ ι (.retained ⟨a, by omega⟩ b))
    (arithmeticThirdEarlierOrientedIso_right hπ data H m j hj u hu b)

end FLT.Mazur.WeierstrassDividedDepth
