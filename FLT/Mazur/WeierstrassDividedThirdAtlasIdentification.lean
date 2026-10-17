/-
Copyright (c) 2026 krandder. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: krandder
-/
module

public import FLT.Mazur.WeierstrassDividedThirdAtlas

/-!
# Actual retained labels in the third atlas

The chart identifications exhibit the installed factors and recover their
old inclusions. No initial chart is identified with an earlier retained node.
-/

@[expose] public noncomputable section
open AlgebraicGeometry CategoryTheory
namespace FLT.Mazur.WeierstrassDividedDepth
open PolygonArithmeticStages PolygonSmoothing WeierstrassModificationX
set_option backward.isDefEq.respectTransparency false
attribute [local irreducible] finiteGlobalModel finiteGlobalContraction
  arithmeticThirdLastOrientedIso arithmeticThirdPrecedingIso arithmeticThirdEarlierOrientedIso
  arithmeticThirdAtlasChart arithmeticSecondJointAtlasChart
variable {R : Type} [CommRing R] [IsDomain R] [IsBezout R]
  {W : WeierstrassCurve R} {π : R} (hπ : π ≠ 0) {n : ℕ}
  (data : (i : Fin (n + 1)) → Data W π (1 + i.val))
  (H : ArithmeticAtlasCoefficients data) (m j : ℕ) (hj : j + 1 ≤ n)
  (u : Rˣ) (hu : (data ⟨j + 1, Nat.lt_succ_of_le hj⟩).b6 = π * ↑u)
local notation "Q" => Quotient R π m
local notation "τ" => arithmeticInitialMobiusSmoothing W H.a1_unit (π ^ 1) π m
local notation "A" => arithmeticThirdAtlasObject hπ data H m j hj u hu
local notation "E" => arithmeticThirdAtlasCorrection hπ data H m j hj u hu
local notation "ι" => arithmeticThirdAtlasChart hπ data H m j hj u hu
local notation "κ" => arithmeticSecondJointAtlasChart hπ data H m j hj u hu
local notation "N" => arithmeticSecondJointLastIdentification hπ data H m j hj u hu
local notation "C" => arithmeticThirdLastOrientedIso hπ data H m j hj u hu

/-- The last label retains the original normalized smoothing. -/
def arithmeticThirdLastIdentification (b : Bool) :
    PolygonSmoothing.chart Q τ ≅ A (.retained ⟨j, by omega⟩ b) :=
  N b ≪≫ eqToIso (by simp only [arithmeticThirdAtlasObject,
    show ¬j + 1 = j by omega, show ¬j + 2 = j by omega, ↓reduceIte])

local notation "L" => arithmeticThirdLastIdentification hπ data H m j hj u hu

omit [IsBezout R] in
/-- The installed last correction is the exact oriented factor between its identifications. -/
theorem arithmeticThirdAtlasCorrection_last (b : Bool) :
    E (.retained ⟨j, by omega⟩ b) = (N b).symm ≪≫ C b ≪≫ L b := by
  simp only [arithmeticThirdAtlasCorrection, arithmeticThirdLastIdentification,
    show ¬j + 1 = j by omega, show ¬j + 2 = j by omega, ↓reduceDIte, ↓reduceIte,
    Iso.trans_assoc]
  rfl

/-- The last full third node recovers its actual old inclusion. -/
@[reassoc] theorem arithmeticThirdLast_chart (b : Bool) :
    (C b).hom ≫ (L b).hom ≫ ι (.retained ⟨j, by omega⟩ b) =
      (N b).hom ≫ κ (.retained ⟨j, by omega⟩ b) := by
  have h := arithmeticThirdAtlasCorrection_chart hπ data H m j hj u hu
    (.retained ⟨j, by omega⟩ b)
  rw [arithmeticThirdAtlasCorrection_last] at h
  have hh := congrArg (fun f ↦ (N b).hom ≫ f) h
  simpa only [Iso.trans_hom, Iso.symm_hom, Category.assoc, Iso.hom_inv_id_assoc] using hh

variable (a : ℕ) (ha : a + 1 = j)
local notation "M" => arithmeticSecondJointPrecedingIdentification hπ data H m j hj u hu a ha
local notation "P" => arithmeticThirdPrecedingIso hπ data H m j hj u hu

/-- The predecessor label has its actual third smoothing. -/
def arithmeticThirdPrecedingIdentification (b : Bool) :
    PolygonSmoothing.chart Q (arithmeticThirdPrecedingSmoothing hπ data H j hj u hu m b) ≅
      A (.retained ⟨a, by omega⟩ b) :=
  eqToIso (by simp only [arithmeticThirdAtlasObject, ha, ↓reduceIte])

local notation "D" => arithmeticThirdPrecedingIdentification hπ data H m j hj u hu a ha

omit [IsBezout R] in
/-- The predecessor is installed on its actual second smoothing. -/
theorem arithmeticThirdAtlasCorrection_preceding (b : Bool) :
    E (.retained ⟨a, by omega⟩ b) = (M b).symm ≪≫ P b ≪≫ D b := by
  simp only [arithmeticThirdAtlasCorrection, ha, ↓reduceDIte]
  rfl

/-- The predecessor comparison recovers its actual second-atlas inclusion. -/
@[reassoc] theorem arithmeticThirdPreceding_chart (b : Bool) :
    (P b).hom ≫ (D b).hom ≫ ι (.retained ⟨a, by omega⟩ b) =
      (M b).hom ≫ κ (.retained ⟨a, by omega⟩ b) := by
  have h := arithmeticThirdAtlasCorrection_chart hπ data H m j hj u hu
    (.retained ⟨a, by omega⟩ b)
  rw [arithmeticThirdAtlasCorrection_preceding hπ data H m j hj u hu a ha b] at h
  have hh := congrArg (fun f ↦ (M b).hom ≫ f) h
  simpa only [Iso.trans_hom, Iso.symm_hom, Category.assoc, Iso.hom_inv_id_assoc] using hh

end FLT.Mazur.WeierstrassDividedDepth
