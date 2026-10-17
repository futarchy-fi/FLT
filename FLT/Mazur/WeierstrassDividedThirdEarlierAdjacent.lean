/-
Copyright (c) 2026 krandder. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: krandder
-/
module

public import FLT.Mazur.WeierstrassDividedThirdEarlierIncoming

/-!
# The next incoming edge in the full third atlas

An unaffected retained chart attaches to the earlier corrected node through
its complete opposite compensation. This edge has no third-layer residual.
-/

@[expose] public noncomputable section
open AlgebraicGeometry CategoryTheory
namespace FLT.Mazur.WeierstrassDividedDepth
open PolygonArithmeticStages PolygonSmoothing WeierstrassModificationX
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
attribute [local irreducible] finiteGlobalModel finiteGlobalContraction
  arithmeticThirdAtlasChart arithmeticThirdEarlierOrientedIso
variable {R : Type} [CommRing R] [IsDomain R] [IsBezout R]
  {W : WeierstrassCurve R} {π : R} (hπ : π ≠ 0) {n : ℕ}
  (data : (i : Fin (n + 1)) → Data W π (1 + i.val))
  (H : ArithmeticAtlasCoefficients data) (m j : ℕ) (hj : j + 1 ≤ n)
  (u : Rˣ) (hu : (data ⟨j + 1, Nat.lt_succ_of_le hj⟩).b6 = π * ↑u)
local notation "Q" => Quotient R π m
local notation "τ" => arithmeticInitialMobiusSmoothing W H.a1_unit (π ^ 1) π m
local notation "A" => arithmeticThirdAtlasObject hπ data H m j hj u hu
local notation "ι" => arithmeticThirdAtlasChart hπ data H m j hj u hu
local notation "κ" => arithmeticSecondJointAtlasChart hπ data H m j hj u hu
local notation "χ" => changedArithmeticAtlasChart hπ data H m j hj u hu
local notation "O" => twistedRetainedOrientation data H m

/-- An earlier unaffected third label is the original normalized full node. -/
def arithmeticThirdUnchangedIdentification (a : Fin (j + 1))
    (ha : a.val + 2 < j) (b : Bool) : PolygonSmoothing.chart Q τ ≅ A (.retained a b) :=
  arithmeticSecondJointEarlierIdentification hπ data H m j hj u hu a (by omega) b ≪≫
    eqToIso (by simp only [arithmeticThirdAtlasObject,
      show ¬a.val + 1 = j by omega, show ¬a.val + 2 = j by omega, ↓reduceIte])

/-- The unaffected third inclusion is the actual original normalized inclusion. -/
@[reassoc] theorem arithmeticThirdUnchanged_chart (a : Fin (j + 1))
    (ha : a.val + 2 < j) (b : Bool) :
    (arithmeticThirdUnchangedIdentification hπ data H m j hj u hu a ha b).hom ≫
      ι (.retained a b) = χ (.retained a b) := by
  have h := arithmeticThirdAtlasCorrection_chart hπ data H m j hj u hu (.retained a b)
  have hh := congrArg (fun f ↦
    (arithmeticSecondJointEarlierIdentification hπ data H m j hj u hu a
      (show a.val + 1 < j by omega) b).hom ≫ f) h
  rw [arithmeticSecondJointEarlier_chart] at hh
  simpa only [arithmeticThirdAtlasCorrection, arithmeticThirdUnchangedIdentification,
    show ¬a.val + 1 = j by omega, show ¬a.val + 2 = j by omega,
    show ¬a.val = j by omega, ↓reduceDIte, ↓reduceIte, Iso.trans_hom,
    Iso.refl_hom, Category.id_comp, Category.assoc] using hh

variable (a : ℕ) (ha : a + 3 = j)
local notation "M" => arithmeticThirdEarlierIdentification
  hπ data H m j hj u hu (a + 1) (by omega)
local notation "N" => arithmeticThirdUnchangedIdentification hπ data H m j hj u hu
local notation "s" => arithmeticThirdEarlierSmoothing hπ data H j hj u hu m

/-- The actual edge into the positive-depth earlier node keeps its full opposite residual. -/
@[reassoc] theorem arithmeticThirdAtlas_earlier_adjacent (b : Bool) :
    leftBranchOpen Q τ ≫ (O b).hom ≫ (N ⟨a, by omega⟩ (show a + 2 < j by omega) b).hom ≫
        ι (.retained ⟨a, by omega⟩ b) =
      (arithmeticThirdEarlierIncomingIso hπ data H m j hj u hu b).hom ≫
        precedingBranch Q (s b) ≫ (M b).hom ≫ ι (.retained ⟨a + 1, by omega⟩ b) := by
  rw [arithmeticThirdUnchanged_chart]
  exact (changedArithmeticAtlas_normalized_adjacent
    hπ data H m j hj u hu a (by omega) b).trans
      (arithmeticThirdEarlier_incoming hπ data H m j hj u hu (a + 1) (by omega) b)

omit m in
/-- On the third layer the remaining positive-depth edge has no Laurent residual. -/
@[reassoc] theorem arithmeticThirdAtlas_earlier_adjacent_third (b : Bool) :
    leftBranchOpen (Quotient R π 3)
        (arithmeticInitialMobiusSmoothing W H.a1_unit (π ^ 1) π 3) ≫
      (twistedRetainedOrientation data H 3 b).hom ≫
        (arithmeticThirdUnchangedIdentification hπ data H 3 j hj u hu
          ⟨a, by omega⟩ (show a + 2 < j by omega) b).hom ≫
            arithmeticThirdAtlasChart hπ data H 3 j hj u hu (.retained ⟨a, by omega⟩ b) =
      precedingBranch (Quotient R π 3)
          (arithmeticThirdEarlierSmoothing hπ data H j hj u hu 3 b) ≫
        (arithmeticThirdEarlierIdentification hπ data H 3 j hj u hu
          (a + 1) (by omega) b).hom ≫
            arithmeticThirdAtlasChart hπ data H 3 j hj u hu
              (.retained ⟨a + 1, by omega⟩ b) := by
  have h := arithmeticThirdAtlas_earlier_adjacent hπ data H 3 j hj u hu a ha b
  rw [arithmeticThirdEarlierIncomingIso_third, Iso.refl_hom, Category.id_comp] at h
  exact h

end FLT.Mazur.WeierstrassDividedDepth
