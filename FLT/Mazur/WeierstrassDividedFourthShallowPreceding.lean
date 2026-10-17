/-
Copyright (c) 2026 krandder. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: krandder
-/
module

public import FLT.Mazur.WeierstrassDividedFourthShallowIdentification
public import FLT.Mazur.WeierstrassDividedFourthOuterPreceding
public import FLT.Mazur.WeierstrassDividedFourthAtlasIdentification

/-!
# The predecessor retained by the fourth depth-two atlas

The depth-two initial replacement leaves the predecessor's fourth factor
intact. Its full node comparison still recovers the third inclusion.
-/

@[expose] public noncomputable section
open AlgebraicGeometry CategoryTheory
namespace FLT.Mazur.WeierstrassDividedDepth
open PolygonArithmeticStages PolygonSmoothing WeierstrassModificationX
set_option backward.isDefEq.respectTransparency false
attribute [local irreducible] finiteGlobalModel finiteGlobalContraction
  arithmeticFourthPrecedingIso arithmeticFourthAtlasCorrection
  arithmeticFourthShallowAtlasChart arithmeticThirdInitialAtlasChart
variable {R : Type} [CommRing R] [IsDomain R] [IsBezout R]
  {W : WeierstrassCurve R} {π : R} (hπ : π ≠ 0) {n : ℕ}
  (data : (i : Fin (n + 1)) → Data W π (1 + i.val))
  (H : ArithmeticAtlasCoefficients data) (m j : ℕ) (hj : j + 1 ≤ n)
  (u : Rˣ) (hu : (data ⟨j + 1, Nat.lt_succ_of_le hj⟩).b6 = π * ↑u)
local notation "Q" => Quotient R π m
local notation "A" => arithmeticFourthShallowAtlasObject hπ data H m j hj u hu
local notation "E" => arithmeticFourthShallowAtlasCorrection hπ data H m j hj u hu
local notation "ι" => arithmeticFourthShallowAtlasChart hπ data H m j hj u hu
local notation "κ" => arithmeticThirdInitialAtlasChart hπ data H m j hj u hu

variable (a : ℕ) (ha : a + 1 = j) (hj₂ : 2 ≤ j)
local notation "N" => arithmeticThirdPrecedingIdentification hπ data H m j hj u hu a ha
local notation "P" => arithmeticFourthPrecedingIso hπ data H m j hj u hu
local notation "D₄" =>
  arithmeticFourthOuterPrecedingIdentification hπ data H m j hj u hu a ha hj₂

/-- At depth at least two the predecessor retains its generic fourth smoothing. -/
def arithmeticFourthShallowPrecedingIdentification (b : Bool) :
    PolygonSmoothing.chart Q (arithmeticFourthPrecedingSmoothing hπ data H j hj u hu m b) ≅
      A (.retained ⟨a, by omega⟩ b) :=
  D₄ b ≪≫ eqToIso (by simp only [arithmeticFourthShallowAtlasObject,
    show ¬(j = 2 ∧ a = 0) by omega, ↓reduceIte])

local notation "D" =>
  arithmeticFourthShallowPrecedingIdentification hπ data H m j hj u hu a ha hj₂

omit [IsBezout R] in
/-- The predecessor correction is the original full fourth factor at its actual label. -/
theorem arithmeticFourthShallowAtlasCorrection_preceding (b : Bool) :
    E (.retained ⟨a, by omega⟩ b) = (N b).symm ≪≫ P b ≪≫ D b := by
  simp only [arithmeticFourthShallowAtlasCorrection,
    show ¬(j = 2 ∧ a = 0) by omega, ↓reduceDIte,
    arithmeticFourthShallowPrecedingIdentification]
  rw [arithmeticFourthOuterAtlasCorrection_preceding hπ data H m j hj u hu a ha hj₂ b]
  simp only [Iso.trans_assoc]

/-- Its installed full node comparison recovers the same third-atlas inclusion. -/
@[reassoc] theorem arithmeticFourthShallowPreceding_chart (b : Bool) :
    (P b).hom ≫ (D b).hom ≫ ι (.retained ⟨a, by omega⟩ b) =
      (N b).hom ≫ κ (.retained ⟨a, by omega⟩ b) := by
  have h := arithmeticFourthShallowAtlasCorrection_chart hπ data H m j hj u hu
    (.retained ⟨a, by omega⟩ b)
  rw [arithmeticFourthShallowAtlasCorrection_preceding hπ data H m j hj u hu a ha hj₂ b] at h
  have hh := congrArg (fun f ↦ (N b).hom ≫ f) h
  simpa only [Iso.trans_hom, Iso.symm_hom, Category.assoc, Iso.hom_inv_id_assoc] using hh

end FLT.Mazur.WeierstrassDividedDepth
