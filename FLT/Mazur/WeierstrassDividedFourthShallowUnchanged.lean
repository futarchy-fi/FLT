/-
Copyright (c) 2026 krandder. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: krandder
-/
module

public import FLT.Mazur.WeierstrassDividedFourthShallowAtlas

/-!
# The unaffected full charts in the fourth depth-two atlas

The terminal, infinity and every retained label outside the depth-two
initial neighbor keep their full fourth geometry and global inclusion.
-/

@[expose] public noncomputable section
open AlgebraicGeometry CategoryTheory
namespace FLT.Mazur.WeierstrassDividedDepth
open PolygonArithmeticStages PolygonSmoothing WeierstrassModificationX
set_option backward.isDefEq.respectTransparency false
attribute [local irreducible] finiteGlobalModel finiteGlobalContraction
  arithmeticFourthShallowIso arithmeticFourthShallowNeighborIso
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

local notation "B" => arithmeticFourthOuterAtlasObject hπ data H m j hj u hu
local notation "χ" => arithmeticFourthOuterAtlasChart hπ data H m j hj u hu
local notation "E₄" => arithmeticFourthOuterAtlasCorrection hπ data H m j hj u hu

/-- An unaffected retained chart keeps exactly its previous full geometry. -/
def arithmeticFourthShallowUnchangedIdentification (a : Fin (j + 1))
    (he : ¬(j = 2 ∧ a.val = 0)) (b : Bool) :
    B (.retained a b) ≅ A (.retained a b) :=
  eqToIso (by simp only [arithmeticFourthShallowAtlasObject, he, ↓reduceIte])

omit [IsBezout R] in
/-- An unaffected label retains exactly its previous fourth factor. -/
theorem arithmeticFourthShallowAtlasCorrection_unchanged (a : Fin (j + 1))
    (he : ¬(j = 2 ∧ a.val = 0)) (b : Bool) :
    E (.retained a b) = E₄ (.retained a b) ≪≫
      arithmeticFourthShallowUnchangedIdentification hπ data H m j hj u hu a he b := by
  simp only [arithmeticFourthShallowAtlasCorrection, he, ↓reduceDIte]
  rfl

/-- The full global inclusion is unchanged outside the two replaced labels. -/
@[reassoc] theorem arithmeticFourthShallowUnchanged_chart (a : Fin (j + 1))
    (he : ¬(j = 2 ∧ a.val = 0)) (b : Bool) :
    (arithmeticFourthShallowUnchangedIdentification hπ data H m j hj u hu a he b).hom ≫
      ι (.retained a b) = χ (.retained a b) := by
  apply (cancel_epi (E₄ (.retained a b)).hom).mp
  rw [← Category.assoc, ← Iso.trans_hom, ← arithmeticFourthShallowAtlasCorrection_unchanged,
    arithmeticFourthShallowAtlasCorrection_chart, arithmeticFourthOuterAtlasCorrection_chart]

/-- The terminal full node retains its fourth inclusion. -/
theorem arithmeticFourthShallowAtlasChart_terminal : ι .terminal = χ .terminal := by
  simp only [arithmeticFourthShallowAtlasChart, arithmeticFourthOuterAtlasChart,
    arithmeticFourthShallowAtlasCorrection]

/-- The original infinity remains in the full global cover with the same map. -/
theorem arithmeticFourthShallowAtlasChart_infinity : ι .infinity = χ .infinity := by
  simp only [arithmeticFourthShallowAtlasChart, arithmeticFourthOuterAtlasChart,
    arithmeticFourthShallowAtlasCorrection]

end FLT.Mazur.WeierstrassDividedDepth
