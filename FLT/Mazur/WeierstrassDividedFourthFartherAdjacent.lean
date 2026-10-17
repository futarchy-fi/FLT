/-
Copyright (c) 2026 krandder. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: krandder
-/
module

public import FLT.Mazur.WeierstrassDividedFourthFartherIncoming

/-!
# The next actual edge beyond the fourth outer factors

An unaffected retained chart attaches to the farther corrected node through
its complete opposite compensation. This edge has no fourth-layer residual.
-/

@[expose] public noncomputable section
open AlgebraicGeometry CategoryTheory
namespace FLT.Mazur.WeierstrassDividedDepth
open PolygonArithmeticStages PolygonSmoothing WeierstrassModificationX
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
attribute [local irreducible] finiteGlobalModel finiteGlobalContraction
  arithmeticFourthOuterAtlasChart arithmeticFourthFartherIso
variable {R : Type} [CommRing R] [IsDomain R] [IsBezout R]
  {W : WeierstrassCurve R} {π : R} (hπ : π ≠ 0) {n : ℕ}
  (data : (i : Fin (n + 1)) → Data W π (1 + i.val))
  (H : ArithmeticAtlasCoefficients data) (m j : ℕ) (hj : j + 1 ≤ n)
  (u : Rˣ) (hu : (data ⟨j + 1, Nat.lt_succ_of_le hj⟩).b6 = π * ↑u)
local notation "Q" => Quotient R π m
local notation "τ" => arithmeticInitialMobiusSmoothing W H.a1_unit (π ^ 1) π m
local notation "A" => arithmeticFourthOuterAtlasObject hπ data H m j hj u hu
local notation "ι" => arithmeticFourthOuterAtlasChart hπ data H m j hj u hu
local notation "κ" => arithmeticSecondJointAtlasChart hπ data H m j hj u hu
local notation "χ" => changedArithmeticAtlasChart hπ data H m j hj u hu
local notation "O" => twistedRetainedOrientation data H m

/-- An unaffected fourth label is the original normalized full node. -/
def arithmeticFourthOuterBeforeIdentification (a : Fin (j + 1))
    (ha : a.val + 3 < j) (b : Bool) : PolygonSmoothing.chart Q τ ≅ A (.retained a b) :=
  arithmeticThirdUnchangedIdentification hπ data H m j hj u hu a (by omega) b ≪≫
    eqToIso (by simp only [arithmeticFourthOuterAtlasObject,
      show ¬a.val + 2 = j by omega, show ¬a.val + 3 = j by omega, ↓reduceIte,
      arithmeticFourthInitialAtlasObject, show ¬(j = 1 ∧ a.val = 0) by omega,
      arithmeticFourthAtlasObject, show ¬a.val + 1 = j by omega,
      arithmeticThirdInitialAtlasObject])

/-- The unaffected fourth inclusion is exactly its original normalized inclusion. -/
@[reassoc] theorem arithmeticFourthOuterBefore_chart (a : Fin (j + 1))
    (ha : a.val + 3 < j) (b : Bool) :
    (arithmeticFourthOuterBeforeIdentification hπ data H m j hj u hu a ha b).hom ≫
      ι (.retained a b) = χ (.retained a b) := by
  have h := arithmeticFourthOuterAtlasCorrection_chart hπ data H m j hj u hu (.retained a b)
  have hh := congrArg (fun f ↦
    (arithmeticThirdUnchangedIdentification hπ data H m j hj u hu a
      (show a.val + 2 < j by omega) b).hom ≫ f) h
  rw [arithmeticThirdInitialAtlasChart_retained, arithmeticThirdUnchanged_chart] at hh
  simpa only [arithmeticFourthOuterAtlasCorrection, arithmeticFourthOuterBeforeIdentification,
    arithmeticFourthInitialAtlasCorrection, arithmeticFourthAtlasCorrection,
    show ¬a.val + 1 = j by omega, show ¬a.val + 2 = j by omega,
    show ¬a.val + 3 = j by omega, show ¬a.val = j by omega,
    show ¬(j = 1 ∧ a.val = 0) by omega, ↓reduceDIte, ↓reduceIte, Iso.trans_hom,
    Iso.refl_hom, Category.id_comp, eqToIso.hom,
    ← Category.assoc, eqToHom_trans] using hh

variable (a : ℕ) (ha : a + 4 = j)
local notation "M" => arithmeticFourthFartherIdentification
  hπ data H m j hj u hu (a + 1) (by omega)
local notation "N" => arithmeticFourthOuterBeforeIdentification hπ data H m j hj u hu
local notation "s" => arithmeticFourthFartherSmoothing hπ data H j hj u hu m

/-- The next actual edge retains the farther node's full opposite compensation. -/
@[reassoc] theorem arithmeticFourthOuterAtlas_farther_adjacent (b : Bool) :
    leftBranchOpen Q τ ≫ (O b).hom ≫ (N ⟨a, by omega⟩ (show a + 3 < j by omega) b).hom ≫
        ι (.retained ⟨a, by omega⟩ b) =
      (arithmeticFourthFartherIncomingIso hπ data H j hj u hu m b).hom ≫
        precedingBranch Q (s b) ≫ (M b).hom ≫ ι (.retained ⟨a + 1, by omega⟩ b) := by
  rw [arithmeticFourthOuterBefore_chart]
  exact (changedArithmeticAtlas_normalized_adjacent
    hπ data H m j hj u hu a (by omega) b).trans
      (arithmeticFourthFarther_incoming hπ data H j hj u hu m (a + 1) (by omega) b)

omit m in
/-- The next complete retained edge also has identity residual on the fourth layer. -/
@[reassoc] theorem arithmeticFourthOuterAtlas_farther_adjacent_fourth (b : Bool) :
    leftBranchOpen (Quotient R π 4)
        (arithmeticInitialMobiusSmoothing W H.a1_unit (π ^ 1) π 4) ≫
      (twistedRetainedOrientation data H 4 b).hom ≫
        (arithmeticFourthOuterBeforeIdentification hπ data H 4 j hj u hu
          ⟨a, by omega⟩ (show a + 3 < j by omega) b).hom ≫
            arithmeticFourthOuterAtlasChart hπ data H 4 j hj u hu (.retained ⟨a, by omega⟩ b) =
      precedingBranch (Quotient R π 4)
          (arithmeticFourthFartherSmoothing hπ data H j hj u hu 4 b) ≫
        (arithmeticFourthFartherIdentification hπ data H 4 j hj u hu
          (a + 1) (by omega) b).hom ≫
            arithmeticFourthOuterAtlasChart hπ data H 4 j hj u hu
              (.retained ⟨a + 1, by omega⟩ b) := by
  have h := arithmeticFourthOuterAtlas_farther_adjacent hπ data H 4 j hj u hu a ha b
  rw [arithmeticFourthFartherIncomingIso_fourth, Iso.refl_hom, Category.id_comp] at h
  exact h

end FLT.Mazur.WeierstrassDividedDepth
