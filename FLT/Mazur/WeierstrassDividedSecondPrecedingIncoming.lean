/-
Copyright (c) 2026 krandder. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: krandder
-/
module

public import FLT.Mazur.WeierstrassDividedSecondPrecedingResidual
public import FLT.Mazur.WeierstrassDividedSecondJointAtlasIncoming

/-!
# The full incoming puncture of the installed predecessor

The remaining opposite substitution is retained at every order, with its
changed smoothing. At stage two its entire incoming square is unchanged.
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
local notation "P" => arithmeticSecondPrecedingOrientedIso hπ data H m j hj u hu
local notation "s" => arithmeticSecondPrecedingSmoothing hπ data H m j hj u hu
local notation "B" => arithmeticSecondPrecedingOpposite hπ data H m j hj u hu

/-- The opposite full substitution in the original reciprocal incoming parameter. -/
def arithmeticSecondPrecedingIncomingIso (b : Bool) : branchTorus Q ≅ branchTorus Q :=
  edgeInversion Q ≪≫ punctureSpecIso (B b) ≪≫ (edgeInversion Q).symm

/-- The full right puncture square keeps the predecessor's exact smoothing. -/
@[reassoc] theorem arithmeticSecondPrecedingOrientedIso_right (b : Bool) :
    (rightBranchOpen Q τ ≫ (O b).hom) ≫ (P b).hom =
      (punctureSpecIso (B b)).hom ≫ rightBranchOpen Q (s b) := by
  rw [Category.assoc, arithmeticSecondPrecedingOrientedIso_hom]
  simpa only [punctureOpen_false, arithmeticSecondPrecedingOpposite] using
    arithmeticSecondPrecedingIso_puncture hπ data H m j hj u hu b false

/-- The same full square in the parameter used by adjacent retained edges. -/
@[reassoc] theorem arithmeticSecondPrecedingOrientedIso_incoming (b : Bool) :
    (precedingBranch Q τ ≫ (O b).hom) ≫ (P b).hom =
      (arithmeticSecondPrecedingIncomingIso hπ data H m j hj u hu b).hom ≫
        precedingBranch Q (s b) := by
  simp only [arithmeticSecondPrecedingIncomingIso, Iso.trans_hom, Iso.symm_hom,
    precedingBranch, Category.assoc, Iso.inv_hom_id_assoc]
  rw [← Category.assoc (rightBranchOpen Q τ), arithmeticSecondPrecedingOrientedIso_right]

omit m in
/-- The entire reciprocal incoming substitution is identity at stage two. -/
theorem arithmeticSecondPrecedingIncomingIso_second (b : Bool) :
    arithmeticSecondPrecedingIncomingIso hπ data H 2 j hj u hu b = Iso.refl _ := by
  rw [arithmeticSecondPrecedingIncomingIso, arithmeticSecondPrecedingOpposite_second,
    punctureSpecIso_refl]
  ext
  simp only [Iso.trans_hom, Iso.refl_hom, Iso.symm_hom]
  change (edgeInversion _).hom ≫ (𝟙 _ ≫ (edgeInversion _).inv) = _
  rw [Category.id_comp, Iso.hom_inv_id]

variable [IsBezout R] (a : ℕ) (ha : a + 1 = j)
local notation "ι" => arithmeticSecondJointAtlasChart hπ data H m j hj u hu
local notation "κ" => arithmeticResidualLiftAtlasChart hπ data H m j hj u hu
local notation "M" => arithmeticSecondJointPrecedingIdentification hπ data H m j hj u hu a ha

/-- The installed predecessor has exactly this full incoming residual. -/
@[reassoc] theorem arithmeticSecondJointPreceding_incoming (b : Bool) :
    precedingBranch Q τ ≫ (O b).hom ≫ κ (.retained ⟨a, by omega⟩ b) =
      (arithmeticSecondPrecedingIncomingIso hπ data H m j hj u hu b).hom ≫
        precedingBranch Q (s b) ≫ (M b).hom ≫ ι (.retained ⟨a, by omega⟩ b) := by
  rw [← arithmeticSecondJointPreceding_chart hπ data H m j hj u hu a ha b]
  simpa only [Category.assoc] using congrArg
    (fun f ↦ f ≫ (M b).hom ≫ ι (.retained ⟨a, by omega⟩ b))
    (arithmeticSecondPrecedingOrientedIso_incoming hπ data H m j hj u hu b)

/-- The direct right puncture gives the boundary form needed at the original initial chart. -/
@[reassoc] theorem arithmeticSecondJointPreceding_right (b : Bool) :
    rightBranchOpen Q τ ≫ (O b).hom ≫ κ (.retained ⟨a, by omega⟩ b) =
      (punctureSpecIso (B b)).hom ≫ rightBranchOpen Q (s b) ≫
        (M b).hom ≫ ι (.retained ⟨a, by omega⟩ b) := by
  rw [← arithmeticSecondJointPreceding_chart hπ data H m j hj u hu a ha b]
  simpa only [Category.assoc] using congrArg
    (fun f ↦ f ≫ (M b).hom ≫ ι (.retained ⟨a, by omega⟩ b))
    (arithmeticSecondPrecedingOrientedIso_right hπ data H m j hj u hu b)

end FLT.Mazur.WeierstrassDividedDepth
