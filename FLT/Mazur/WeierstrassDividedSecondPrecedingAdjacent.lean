/-
Copyright (c) 2026 krandder. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: krandder
-/
module

public import FLT.Mazur.WeierstrassDividedSecondPrecedingIncoming

/-!
# The remaining predecessor edge in the full second atlas

Below the two corrected retained nodes the original normalized chart remains
unchanged. Its next edge carries exactly the predecessor's opposite residual.
-/

@[expose] public noncomputable section
open AlgebraicGeometry CategoryTheory
namespace FLT.Mazur.WeierstrassDividedDepth
open PolygonArithmeticStages PolygonSmoothing WeierstrassModificationX
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
attribute [local irreducible] finiteGlobalModel finiteGlobalContraction
  arithmeticSecondJointAtlasChart arithmeticSecondPrecedingOrientedIso
variable {R : Type} [CommRing R] [IsDomain R] [IsBezout R]
  {W : WeierstrassCurve R} {π : R} (hπ : π ≠ 0) {n : ℕ}
  (data : (i : Fin (n + 1)) → Data W π (1 + i.val))
  (H : ArithmeticAtlasCoefficients data) (m j : ℕ) (hj : j + 1 ≤ n)
  (u : Rˣ) (hu : (data ⟨j + 1, Nat.lt_succ_of_le hj⟩).b6 = π * ↑u)
local notation "Q" => Quotient R π m
local notation "τ" => arithmeticInitialMobiusSmoothing W H.a1_unit (π ^ 1) π m
local notation "A" => arithmeticSecondJointAtlasObject hπ data H m j hj u hu
local notation "ι" => arithmeticSecondJointAtlasChart hπ data H m j hj u hu
local notation "κ" => arithmeticResidualLiftAtlasChart hπ data H m j hj u hu
local notation "χ" => changedArithmeticAtlasChart hπ data H m j hj u hu
local notation "O" => twistedRetainedOrientation data H m

/-- A chart strictly before the last retained node has no first lifted correction. -/
theorem arithmeticResidualLiftAtlasChart_before (a : Fin (j + 1))
    (ha : a.val < j) (b : Bool) : κ (.retained a b) = χ (.retained a b) := by
  simp only [arithmeticResidualLiftAtlasChart, arithmeticResidualLiftAtlasCorrection,
    show ¬a.val = j by omega, ↓reduceIte, Iso.refl_inv]
  change 𝟙 _ ≫ χ (.retained a b) = _
  exact Category.id_comp _

/-- Identify an earlier unaffected chart with the same normalized full node. -/
def arithmeticSecondJointEarlierIdentification (a : Fin (j + 1))
    (ha : a.val + 1 < j) (b : Bool) : PolygonSmoothing.chart Q τ ≅ A (.retained a b) :=
  eqToIso (by
    simp only [arithmeticSecondJointAtlasObject, show ¬a.val + 1 = j by omega, ↓reduceIte]
    rfl)

/-- Its inclusion is exactly the original normalized inclusion. -/
@[reassoc] theorem arithmeticSecondJointEarlier_chart (a : Fin (j + 1))
    (ha : a.val + 1 < j) (b : Bool) :
    (arithmeticSecondJointEarlierIdentification hπ data H m j hj u hu a ha b).hom ≫
      ι (.retained a b) = χ (.retained a b) := by
  have h := arithmeticSecondJointAtlasCorrection_chart hπ data H m j hj u hu (.retained a b)
  rw [arithmeticResidualLiftAtlasChart_before hπ data H m j hj u hu a (by omega) b] at h
  simpa only [arithmeticSecondJointAtlasCorrection, show ¬a.val + 1 = j by omega,
    show ¬a.val = j by omega, ↓reduceDIte, ↓reduceIte, Iso.trans_hom, Iso.refl_hom,
    Category.id_comp, arithmeticSecondJointEarlierIdentification] using h

variable (a : ℕ) (ha : a + 2 = j)
local notation "M" => arithmeticSecondJointPrecedingIdentification
  hπ data H m j hj u hu (a + 1) (by omega)
local notation "N" => arithmeticSecondJointEarlierIdentification hπ data H m j hj u hu
local notation "s" => arithmeticSecondPrecedingSmoothing hπ data H m j hj u hu

/-- The actual edge into a positive-depth predecessor keeps its full opposite residual. -/
@[reassoc] theorem arithmeticSecondJointAtlas_preceding_adjacent (b : Bool) :
    leftBranchOpen Q τ ≫ (O b).hom ≫ (N ⟨a, by omega⟩ (show a + 1 < j by omega) b).hom ≫
        ι (.retained ⟨a, by omega⟩ b) =
      (arithmeticSecondPrecedingIncomingIso hπ data H m j hj u hu b).hom ≫
        precedingBranch Q (s b) ≫ (M b).hom ≫ ι (.retained ⟨a + 1, by omega⟩ b) := by
  rw [arithmeticSecondJointEarlier_chart]
  have h := changedArithmeticAtlas_normalized_adjacent hπ data H m j hj u hu a (by omega) b
  rw [← arithmeticResidualLiftAtlasChart_before hπ data H m j hj u hu
    ⟨a + 1, by omega⟩ (show a + 1 < j by omega) b] at h
  exact h.trans (arithmeticSecondJointPreceding_incoming
    hπ data H m j hj u hu (a + 1) (by omega) b)

omit m in
/-- At stage two the remaining positive-depth edge has no Laurent residual. -/
@[reassoc] theorem arithmeticSecondJointAtlas_preceding_adjacent_second (b : Bool) :
    leftBranchOpen (Quotient R π 2)
        (arithmeticInitialMobiusSmoothing W H.a1_unit (π ^ 1) π 2) ≫
      (twistedRetainedOrientation data H 2 b).hom ≫
        (arithmeticSecondJointEarlierIdentification hπ data H 2 j hj u hu
          ⟨a, by omega⟩ (show a + 1 < j by omega) b).hom ≫
            arithmeticSecondJointAtlasChart hπ data H 2 j hj u hu (.retained ⟨a, by omega⟩ b) =
      precedingBranch (Quotient R π 2)
          (arithmeticSecondPrecedingSmoothing hπ data H 2 j hj u hu b) ≫
        (arithmeticSecondJointPrecedingIdentification hπ data H 2 j hj u hu
          (a + 1) (by omega) b).hom ≫
            arithmeticSecondJointAtlasChart hπ data H 2 j hj u hu
              (.retained ⟨a + 1, by omega⟩ b) := by
  have h := arithmeticSecondJointAtlas_preceding_adjacent hπ data H 2 j hj u hu a ha b
  rw [arithmeticSecondPrecedingIncomingIso_second, Iso.refl_hom, Category.id_comp] at h
  exact h

end FLT.Mazur.WeierstrassDividedDepth
