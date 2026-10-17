/-
Copyright (c) 2026 krandder. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: krandder
-/
module

public import FLT.Mazur.WeierstrassDividedFourthOuterAtlas

/-!
# Actual labels of the simultaneous outer fourth factors

Both factors recover their precise third-atlas inclusions. The farther
comparison explicitly retains the original normalized coordinate orientation.
-/

@[expose] public noncomputable section
open AlgebraicGeometry CategoryTheory
namespace FLT.Mazur.WeierstrassDividedDepth
open PolygonArithmeticStages PolygonSmoothing WeierstrassModificationX
set_option backward.isDefEq.respectTransparency false
attribute [local irreducible] finiteGlobalModel finiteGlobalContraction
  arithmeticFourthOuterIso arithmeticFourthFartherIso
  arithmeticFourthOuterAtlasChart arithmeticThirdInitialAtlasChart
variable {R : Type} [CommRing R] [IsDomain R] [IsBezout R]
  {W : WeierstrassCurve R} {π : R} (hπ : π ≠ 0) {n : ℕ}
  (data : (i : Fin (n + 1)) → Data W π (1 + i.val))
  (H : ArithmeticAtlasCoefficients data) (m j : ℕ) (hj : j + 1 ≤ n)
  (u : Rˣ) (hu : (data ⟨j + 1, Nat.lt_succ_of_le hj⟩).b6 = π * ↑u)
local notation "Q" => Quotient R π m
local notation "A" => arithmeticFourthOuterAtlasObject hπ data H m j hj u hu
local notation "E" => arithmeticFourthOuterAtlasCorrection hπ data H m j hj u hu
local notation "ι" => arithmeticFourthOuterAtlasChart hπ data H m j hj u hu
local notation "κ" => arithmeticThirdInitialAtlasChart hπ data H m j hj u hu

variable (a : ℕ)
section Earlier
variable (ha : a + 2 = j)
local notation "N" => arithmeticThirdEarlierIdentification hπ data H m j hj u hu a ha
local notation "P" => arithmeticFourthOuterIso hπ data H j hj u hu m

/-- The earlier actual label has the smoothing of the simultaneous whole-node factor. -/
def arithmeticFourthOuterIdentification (b : Bool) :
    PolygonSmoothing.chart Q (arithmeticFourthOuterSmoothing hπ data H j hj u hu m b) ≅
      A (.retained ⟨a, by omega⟩ b) :=
  eqToIso (by simp only [arithmeticFourthOuterAtlasObject, ha, ↓reduceIte])

local notation "D" => arithmeticFourthOuterIdentification hπ data H m j hj u hu a ha

omit [IsBezout R] in
/-- The earlier replacement is installed directly from its third smoothing. -/
theorem arithmeticFourthOuterAtlasCorrection_earlier (b : Bool) :
    E (.retained ⟨a, by omega⟩ b) = (N b).symm ≪≫ P b ≪≫ D b := by
  simp only [arithmeticFourthOuterAtlasCorrection, ha, ↓reduceDIte]
  rfl

/-- The installed simultaneous earlier factor recovers the third global inclusion. -/
@[reassoc] theorem arithmeticFourthOuter_chart (b : Bool) :
    (P b).hom ≫ (D b).hom ≫ ι (.retained ⟨a, by omega⟩ b) =
      (N b).hom ≫
        κ (.retained ⟨a, by omega⟩ b) := by
  have h := arithmeticFourthOuterAtlasCorrection_chart hπ data H m j hj u hu
    (.retained ⟨a, by omega⟩ b)
  rw [arithmeticFourthOuterAtlasCorrection_earlier hπ data H m j hj u hu a ha b] at h
  have hh := congrArg (fun f ↦ (N b).hom ≫ f) h
  simpa only [Iso.trans_hom, Iso.symm_hom, Category.assoc, Iso.hom_inv_id_assoc] using hh

end Earlier

variable (hf : a + 3 = j)
local notation "M" => arithmeticThirdUnchangedIdentification hπ data H m j hj u hu
local notation "F" => arithmeticFourthFartherIso hπ data H j hj u hu m
local notation "O" => twistedRetainedOrientation data H m

/-- The farther retained label has its new full positive-factor smoothing. -/
def arithmeticFourthFartherIdentification (b : Bool) :
    PolygonSmoothing.chart Q (arithmeticFourthFartherSmoothing hπ data H j hj u hu m b) ≅
      A (.retained ⟨a, by omega⟩ b) :=
  eqToIso (by simp only [arithmeticFourthOuterAtlasObject,
    show ¬a + 2 = j by omega, hf, ↓reduceIte])

local notation "L" => arithmeticFourthFartherIdentification hπ data H m j hj u hu a hf

omit [IsBezout R] in
/-- The farther factor starts in the actual oriented normalized coordinate. -/
theorem arithmeticFourthOuterAtlasCorrection_farther (b : Bool) :
    E (.retained ⟨a, by omega⟩ b) =
      (M ⟨a, by omega⟩ (show a + 2 < j by omega) b).symm ≪≫ (O b).symm ≪≫ F b ≪≫ L b := by
  simp only [arithmeticFourthOuterAtlasCorrection,
    show ¬a + 2 = j by omega, hf, ↓reduceDIte]
  rfl

/-- The installed farther factor recovers its oriented third-atlas inclusion. -/
@[reassoc] theorem arithmeticFourthFarther_chart (b : Bool) :
    (F b).hom ≫ (L b).hom ≫ ι (.retained ⟨a, by omega⟩ b) =
      (O b).hom ≫ (M ⟨a, by omega⟩ (show a + 2 < j by omega) b).hom ≫
        κ (.retained ⟨a, by omega⟩ b) := by
  have h := arithmeticFourthOuterAtlasCorrection_chart hπ data H m j hj u hu
    (.retained ⟨a, by omega⟩ b)
  rw [arithmeticFourthOuterAtlasCorrection_farther hπ data H m j hj u hu a hf b] at h
  have hh := congrArg (fun f ↦ (O b).hom ≫
    (M ⟨a, by omega⟩ (show a + 2 < j by omega) b).hom ≫ f) h
  simpa only [Iso.trans_hom, Iso.symm_hom, Category.assoc, Iso.hom_inv_id_assoc] using hh

end FLT.Mazur.WeierstrassDividedDepth
