/-
Copyright (c) 2026 krandder. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: krandder
-/
module

public import FLT.Mazur.WeierstrassDividedTwoFiniteGeometry
public import FLT.Mazur.WeierstrassDividedTwoFiniteResiduals

/-!
# Finite outgoing transitions of all three retained nodes

Conjugate the outgoing puncture of the same whole retained factor into the closing
coordinate. Keep both the fifth and finite full node parameters.
-/

@[expose] public noncomputable section
open AlgebraicGeometry CategoryTheory
namespace FLT.Mazur.WeierstrassDividedDepth
open PolygonArithmeticStages PolygonSmoothing WeierstrassModificationX
set_option backward.isDefEq.respectTransparency false
variable {R : Type} [CommRing R] [IsDomain R] {W : WeierstrassCurve R} {π : R}
  (hπ : π ≠ 0) {n : ℕ} (data : (i : Fin (n + 1)) → Data W π (1 + i.val))
  (H : ArithmeticAtlasCoefficients data) (k m : ℕ) (hj : 3 ≤ n)
  (u : Rˣ) (hu : (data ⟨3, Nat.lt_succ_of_le hj⟩).b6 = π * ↑u)
local notation "Q" => Quotient R π m
local notation "τ" => PolygonArithmeticRetainedChain.State.retained
  (arithmeticTwoSeedState hπ data H hj u hu) m
local notation "s" => PolygonArithmeticRetainedChain.State.retained
  (arithmeticTwoFiniteState hπ data H hj u hu k) m
local notation "C" => arithmeticTwoFiniteRetainedIso hπ data H k m hj u hu
variable (i : Fin 3)

/-- The outgoing substitution in the original inverse closing coordinate. -/
def arithmeticTwoFiniteOutgoingIso (b : Bool) : branchTorus Q ≅ branchTorus Q :=
  edgeInversion Q ≪≫ punctureSpecIso
    (arithmeticTwoFiniteRetainedPunctureEquiv hπ data H hj u hu k m i b true) ≪≫
      (edgeInversion Q).symm

local notation "K" => arithmeticTwoFiniteOutgoingIso hπ data H k m hj u hu i

/-- The algebraic conjugate is the same full geometric substitution. -/
theorem arithmeticTwoFiniteOutgoingEquiv_spec (b : Bool) :
    punctureSpecIso (arithmeticTwoFiniteOutgoingEquiv hπ data H hj u hu k m i b) = K b := by
  simp only [arithmeticTwoFiniteOutgoingEquiv, punctureSpecIso_trans,
    punctureSpecIso_invert, arithmeticTwoFiniteOutgoingIso]
  rfl

/-- The old closing inclusion passes through the full changed-smoothing retained node. -/
@[reassoc] theorem arithmeticTwoFiniteRetainedIso_closing (b : Bool) :
    (edgeInversion Q).hom ≫ leftBranchOpen Q (τ i b) ≫ (C i b).hom =
      (K b).hom ≫ (edgeInversion Q).hom ≫ leftBranchOpen Q (s i b) := by
  have h := arithmeticTwoFiniteRetainedIso_puncture hπ data H k m hj u hu i b true
  simp only [punctureOpen_true] at h
  simp only [arithmeticTwoFiniteOutgoingIso, Iso.trans_hom, Iso.symm_hom,
    Category.assoc, Iso.inv_hom_id_assoc]
  rw [h]

end FLT.Mazur.WeierstrassDividedDepth
