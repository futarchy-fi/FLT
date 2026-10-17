/-
Copyright (c) 2026 krandder. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: krandder
-/
module

public import FLT.Mazur.WeierstrassDividedFourthInitialIdentification

/-!
# The last and terminal labels retain their fourth corrections

Replacing the initial and predecessor factors leaves the last retained label
and terminal untouched. Their global inclusions still recover the third atlas.
-/

@[expose] public noncomputable section
open AlgebraicGeometry CategoryTheory
namespace FLT.Mazur.WeierstrassDividedDepth
open PolygonArithmeticStages PolygonSmoothing WeierstrassModificationX
set_option backward.isDefEq.respectTransparency false
attribute [local irreducible] finiteGlobalModel finiteGlobalContraction
  arithmeticFourthLastOrientedIso arithmeticFourthAtlasCorrection
  arithmeticFourthInitialAtlasChart arithmeticFourthAtlasChart arithmeticThirdInitialAtlasChart
variable {R : Type} [CommRing R] [IsDomain R] [IsBezout R]
  {W : WeierstrassCurve R} {π : R} (hπ : π ≠ 0) {n : ℕ}
  (data : (i : Fin (n + 1)) → Data W π (1 + i.val))
  (H : ArithmeticAtlasCoefficients data) (m j : ℕ) (hj : j + 1 ≤ n)
  (u : Rˣ) (hu : (data ⟨j + 1, Nat.lt_succ_of_le hj⟩).b6 = π * ↑u)
local notation "Q" => Quotient R π m
local notation "τ" => arithmeticInitialMobiusSmoothing W H.a1_unit (π ^ 1) π m
local notation "A" => arithmeticFourthInitialAtlasObject hπ data H m j hj u hu
local notation "E" => arithmeticFourthInitialAtlasCorrection hπ data H m j hj u hu
local notation "ι" => arithmeticFourthInitialAtlasChart hπ data H m j hj u hu
local notation "κ" => arithmeticThirdInitialAtlasChart hπ data H m j hj u hu
local notation "N" => arithmeticThirdLastIdentification hπ data H m j hj u hu
local notation "L₄" => arithmeticFourthLastIdentification hπ data H m j hj u hu
local notation "C" => arithmeticFourthLastOrientedIso hπ data H m j hj u hu

/-- The last retained label keeps its complete fourth identification. -/
def arithmeticFourthInitialLastIdentification (b : Bool) :
    PolygonSmoothing.chart Q τ ≅ A (.retained ⟨j, by omega⟩ b) :=
  L₄ b ≪≫ eqToIso (by simp only [arithmeticFourthInitialAtlasObject,
    show ¬(j = 1 ∧ j = 0) by omega, ↓reduceIte])

local notation "L" => arithmeticFourthInitialLastIdentification hπ data H m j hj u hu

omit [IsBezout R] in
/-- The last factor is exactly the same oriented fourth correction. -/
theorem arithmeticFourthInitialAtlasCorrection_last (b : Bool) :
    E (.retained ⟨j, by omega⟩ b) = (N b).symm ≪≫ C b ≪≫ L b := by
  simp only [arithmeticFourthInitialAtlasCorrection,
    show ¬(j = 1 ∧ j = 0) by omega, ↓reduceDIte,
    arithmeticFourthAtlasCorrection_last, arithmeticFourthInitialLastIdentification,
    Iso.trans_assoc]

/-- The last node's full comparison recovers its actual third inclusion. -/
@[reassoc] theorem arithmeticFourthInitialLast_chart (b : Bool) :
    (C b).hom ≫ (L b).hom ≫ ι (.retained ⟨j, by omega⟩ b) =
      (N b).hom ≫ κ (.retained ⟨j, by omega⟩ b) := by
  have h := arithmeticFourthInitialAtlasCorrection_chart hπ data H m j hj u hu
    (.retained ⟨j, by omega⟩ b)
  rw [arithmeticFourthInitialAtlasCorrection_last] at h
  have hh := congrArg (fun f ↦ (N b).hom ≫ f) h
  simpa only [Iso.trans_hom, Iso.symm_hom, Category.assoc, Iso.hom_inv_id_assoc] using hh

/-- The installed last chart agrees with the original fourth chart under its identification. -/
@[reassoc] theorem arithmeticFourthInitialLast_chart_eq (b : Bool) :
    (L b).hom ≫ ι (.retained ⟨j, by omega⟩ b) =
      (L₄ b).hom ≫ arithmeticFourthAtlasChart hπ data H m j hj u hu
        (.retained ⟨j, by omega⟩ b) := by
  apply (cancel_epi (C b).hom).mp
  rw [arithmeticFourthInitialLast_chart, arithmeticFourthLast_chart]

/-- The terminal chart retains its full fourth inclusion. -/
theorem arithmeticFourthInitialAtlasChart_terminal :
    ι .terminal = arithmeticFourthAtlasChart hπ data H m j hj u hu .terminal := by
  simp only [arithmeticFourthInitialAtlasChart, arithmeticFourthAtlasChart,
    arithmeticFourthInitialAtlasCorrection]

/-- The infinity chart retains its full original inclusion. -/
theorem arithmeticFourthInitialAtlasChart_infinity :
    ι .infinity = arithmeticFourthAtlasChart hπ data H m j hj u hu .infinity := by
  simp only [arithmeticFourthInitialAtlasChart, arithmeticFourthAtlasChart,
    arithmeticFourthInitialAtlasCorrection]

end FLT.Mazur.WeierstrassDividedDepth
