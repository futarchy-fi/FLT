/-
Copyright (c) 2026 krandder. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: krandder
-/
module

public import FLT.Mazur.WeierstrassDividedThirdAtlasClosing
public import FLT.Mazur.WeierstrassDividedThirdIncomingCancellation

/-!
# The actual incoming edges of the third atlas

The same last factor serves the closing and incoming edges. Its predecessor
keeps all second and third smoothing drifts in the global diagram.
-/

@[expose] public noncomputable section
open AlgebraicGeometry CategoryTheory
namespace FLT.Mazur.WeierstrassDividedDepth
open PolygonArithmeticStages PolygonSmoothing WeierstrassModificationX
set_option backward.isDefEq.respectTransparency false
attribute [local irreducible] finiteGlobalModel finiteGlobalContraction
  arithmeticThirdPrecedingIso arithmeticThirdAtlasChart
variable {R : Type} [CommRing R] [IsDomain R] [IsBezout R]
  {W : WeierstrassCurve R} {π : R} (hπ : π ≠ 0) {n : ℕ}
  (data : (i : Fin (n + 1)) → Data W π (1 + i.val))
  (H : ArithmeticAtlasCoefficients data) (m j : ℕ) (hj : j + 1 ≤ n)
  (u : Rˣ) (hu : (data ⟨j + 1, Nat.lt_succ_of_le hj⟩).b6 = π * ↑u)
  (a : ℕ) (ha : a + 1 = j)
local notation "Q" => Quotient R π m
local notation "τ" => arithmeticInitialMobiusSmoothing W H.a1_unit (π ^ 1) π m
local notation "ι" => arithmeticThirdAtlasChart hπ data H m j hj u hu
local notation "κ" => arithmeticSecondJointAtlasChart hπ data H m j hj u hu
local notation "P" => arithmeticThirdPrecedingIso hπ data H m j hj u hu
local notation "O" => twistedRetainedOrientation data H m
local notation "N" => arithmeticThirdLastIdentification hπ data H m j hj u hu
local notation "M" => arithmeticThirdPrecedingIdentification hπ data H m j hj u hu a ha
local notation "N₂" => arithmeticSecondJointLastIdentification hπ data H m j hj u hu
local notation "M₂" => arithmeticSecondJointPrecedingIdentification hπ data H m j hj u hu a ha
local notation "s" => arithmeticThirdPrecedingSmoothing hπ data H j hj u hu m
local notation "s₂" => arithmeticSecondPrecedingSmoothing hπ data H m j hj u hu
local notation "V" => arithmeticThirdPrecedingIntegralField hπ data H j hj u hu

/-- The installed incoming edge has exactly the full third algebraic residual. -/
@[reassoc] theorem arithmeticThirdAtlas_residual_incoming (b : Bool) :
    leftBranchOpen Q (s b) ≫ (M b).hom ≫ ι (.retained ⟨a, by omega⟩ b) =
      (arithmeticThirdIncomingResidual hπ data H m j hj u hu b).hom ≫
        precedingBranch Q τ ≫ (O b).hom ≫ (N b).hom ≫
          ι (.retained ⟨j, by omega⟩ b) := by
  apply (cancel_epi
    (punctureSpecIso (twoBranchCorrectionPunctureFactor R π m (s₂ b) (V b) true)).hom).mp
  calc
    _ = leftBranchOpen Q (s₂ b) ≫ (M₂ b).hom ≫ κ (.retained ⟨a, by omega⟩ b) := by
      rw [← Category.assoc _ (leftBranchOpen Q (s b)),
        ← arithmeticThirdPrecedingIso_outgoing, Category.assoc,
        arithmeticThirdPreceding_chart]
    _ = (arithmeticSecondJointIncomingResidual hπ data H m j hj u hu b).hom ≫
        precedingBranch Q τ ≫ (O b).hom ≫ (N₂ b).hom ≫
          κ (.retained ⟨j, by omega⟩ b) :=
      arithmeticSecondJointAtlas_residual_incoming hπ data H m j hj u hu a ha b
    _ = _ := by
      simp only [arithmeticThirdIncomingResidual, Iso.trans_hom, Iso.symm_hom,
        Category.assoc, Iso.hom_inv_id_assoc]
      rw [← arithmeticThirdLastOrientedIso_incoming_assoc,
        arithmeticThirdLast_chart]

omit m in
/-- Both actual incoming edges have identity residual on the third layer. -/
@[reassoc] theorem arithmeticThirdAtlas_incoming_third (b : Bool) :
    leftBranchOpen (Quotient R π 3)
        (arithmeticThirdPrecedingSmoothing hπ data H j hj u hu 3 b) ≫
      (arithmeticThirdPrecedingIdentification hπ data H 3 j hj u hu a ha b).hom ≫
        arithmeticThirdAtlasChart hπ data H 3 j hj u hu (.retained ⟨a, by omega⟩ b) =
      precedingBranch (Quotient R π 3)
          (arithmeticInitialMobiusSmoothing W H.a1_unit (π ^ 1) π 3) ≫
        (twistedRetainedOrientation data H 3 b).hom ≫
          (arithmeticThirdLastIdentification hπ data H 3 j hj u hu b).hom ≫
            arithmeticThirdAtlasChart hπ data H 3 j hj u hu (.retained ⟨j, by omega⟩ b) := by
  have h := arithmeticThirdAtlas_residual_incoming hπ data H 3 j hj u hu a ha b
  rw [← arithmeticThirdIncomingEquiv_spec, arithmeticThirdIncomingEquiv_third,
    punctureSpecIso_refl, Iso.refl_hom] at h
  simpa only [branchTorus, Category.id_comp] using h

end FLT.Mazur.WeierstrassDividedDepth
