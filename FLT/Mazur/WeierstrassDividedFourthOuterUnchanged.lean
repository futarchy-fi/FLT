/-
Copyright (c) 2026 krandder. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: krandder
-/
module

public import FLT.Mazur.WeierstrassDividedFourthOuterAtlas

/-!
# The unaffected full charts in the fourth outer atlas

The initial, terminal, infinity and every retained label outside the two
new factors keep their fourth initial geometry and global inclusion.
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

local notation "B" => arithmeticFourthInitialAtlasObject hπ data H m j hj u hu
local notation "χ" => arithmeticFourthInitialAtlasChart hπ data H m j hj u hu
local notation "E₄" => arithmeticFourthInitialAtlasCorrection hπ data H m j hj u hu

/-- An unaffected retained chart keeps exactly its previous full geometry. -/
def arithmeticFourthOuterUnchangedIdentification (a : Fin (j + 1))
    (he : a.val + 2 ≠ j) (hf : a.val + 3 ≠ j) (b : Bool) :
    B (.retained a b) ≅ A (.retained a b) :=
  eqToIso (by simp only [arithmeticFourthOuterAtlasObject, he, hf, ↓reduceIte])

omit [IsBezout R] in
/-- An unaffected label retains exactly its previous fourth factor. -/
theorem arithmeticFourthOuterAtlasCorrection_unchanged (a : Fin (j + 1))
    (he : a.val + 2 ≠ j) (hf : a.val + 3 ≠ j) (b : Bool) :
    E (.retained a b) = E₄ (.retained a b) ≪≫
      arithmeticFourthOuterUnchangedIdentification hπ data H m j hj u hu a he hf b := by
  simp only [arithmeticFourthOuterAtlasCorrection, he, hf, ↓reduceDIte]
  rfl

/-- The full global inclusion is unchanged outside the two replaced labels. -/
@[reassoc] theorem arithmeticFourthOuterUnchanged_chart (a : Fin (j + 1))
    (he : a.val + 2 ≠ j) (hf : a.val + 3 ≠ j) (b : Bool) :
    (arithmeticFourthOuterUnchangedIdentification hπ data H m j hj u hu a he hf b).hom ≫
      ι (.retained a b) = χ (.retained a b) := by
  apply (cancel_epi (E₄ (.retained a b)).hom).mp
  rw [← Category.assoc, ← Iso.trans_hom, ← arithmeticFourthOuterAtlasCorrection_unchanged,
    arithmeticFourthOuterAtlasCorrection_chart, arithmeticFourthInitialAtlasCorrection_chart]

/-- Both full original initial opens retain their previous global inclusions. -/
theorem arithmeticFourthOuterAtlasChart_initial (b : Bool) : ι (.initial b) = χ (.initial b) := by
  simp only [arithmeticFourthOuterAtlasChart, arithmeticFourthInitialAtlasChart,
    arithmeticFourthOuterAtlasCorrection]

/-- The terminal full node retains its fourth inclusion. -/
theorem arithmeticFourthOuterAtlasChart_terminal : ι .terminal = χ .terminal := by
  simp only [arithmeticFourthOuterAtlasChart, arithmeticFourthInitialAtlasChart,
    arithmeticFourthOuterAtlasCorrection]

/-- The original infinity remains in the full global cover with the same map. -/
theorem arithmeticFourthOuterAtlasChart_infinity : ι .infinity = χ .infinity := by
  simp only [arithmeticFourthOuterAtlasChart, arithmeticFourthInitialAtlasChart,
    arithmeticFourthOuterAtlasCorrection]

end FLT.Mazur.WeierstrassDividedDepth
