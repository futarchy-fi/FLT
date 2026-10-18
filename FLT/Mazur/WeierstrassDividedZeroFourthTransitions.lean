/-
Copyright (c) 2026 krandder. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: krandder
-/
module

public import FLT.Mazur.WeierstrassDividedZeroFourthGeometry
public import FLT.Mazur.WeierstrassDividedZeroFourthCancellation

/-!
# The fourth depth-zero outgoing transition with its changed smoothing

Conjugate the outgoing puncture of the same whole last factor into the closing
coordinate. Keep both the third and fourth full node parameters.
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
local notation "τ" => arithmeticZeroThirdLastSmoothing hπ data H j hj u hu m
local notation "s" => arithmeticZeroFourthLastSmoothing hπ data H j hj u hu m
local notation "C" => arithmeticZeroFourthLastIso hπ data H m j hj u hu

/-- The outgoing substitution in the original inverse closing coordinate. -/
def arithmeticZeroFourthLastEdgeIso (b : Bool) : branchTorus Q ≅ branchTorus Q :=
  edgeInversion Q ≪≫ punctureSpecIso (twoBranchCorrectionPunctureFactor R π m (τ b)
    (arithmeticZeroFourthLastIntegralField hπ data H j hj u hu b) true) ≪≫
      (edgeInversion Q).symm

local notation "K" => arithmeticZeroFourthLastEdgeIso hπ data H m j hj u hu

/-- The algebraic conjugate is the same full geometric substitution. -/
theorem arithmeticZeroFourthLastEdgeEquiv_spec (b : Bool) :
    punctureSpecIso (arithmeticZeroFourthLastEdgeEquiv hπ data H j hj u hu m b) = K b := by
  simp only [arithmeticZeroFourthLastEdgeEquiv, punctureSpecIso_trans,
    punctureSpecIso_invert, arithmeticZeroFourthLastEdgeIso]
  rfl

/-- The old closing inclusion passes through the full changed-smoothing last node. -/
@[reassoc] theorem arithmeticZeroFourthLastIso_closing (b : Bool) :
    (edgeInversion Q).hom ≫ leftBranchOpen Q (τ b) ≫ (C b).hom =
      (K b).hom ≫ (edgeInversion Q).hom ≫ leftBranchOpen Q (s b) := by
  have h := arithmeticZeroFourthLastIso_puncture hπ data H m j hj u hu b true
  simp only [punctureOpen_true] at h
  simp only [arithmeticZeroFourthLastEdgeIso, Iso.trans_hom, Iso.symm_hom,
    Category.assoc, Iso.inv_hom_id_assoc]
  rw [h]

end FLT.Mazur.WeierstrassDividedDepth
