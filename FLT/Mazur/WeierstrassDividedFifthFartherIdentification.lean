/-
Copyright (c) 2026 krandder. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: krandder
-/
module

public import FLT.Mazur.WeierstrassDividedFifthFartherAtlas
public import FLT.Mazur.WeierstrassDividedFourthFartherInitial

/-!
# Actual labels of the fifth depth-three initial atlas

The initial open and its neighbor are identified with their installed full
fifth objects. Both comparisons recover their actual fourth inclusions.
-/

@[expose] public noncomputable section
open AlgebraicGeometry CategoryTheory
namespace FLT.Mazur.WeierstrassDividedDepth
open PolygonArithmeticStages PolygonSmoothing WeierstrassModificationX
set_option backward.isDefEq.respectTransparency false
attribute [local irreducible] finiteGlobalModel finiteGlobalContraction
  arithmeticFifthFartherIso arithmeticFifthFartherNeighborIso arithmeticFourthOuterAtlasCorrection
  arithmeticFifthFartherAtlasChart arithmeticFourthOuterAtlasChart
variable {R : Type} [CommRing R] [IsDomain R] [IsBezout R]
  {W : WeierstrassCurve R} {π : R} (hπ : π ≠ 0) {n : ℕ}
  (data : (i : Fin (n + 1)) → Data W π (1 + i.val))
  (H : ArithmeticAtlasCoefficients data) (m j : ℕ) (hj : j + 1 ≤ n)
  (u : Rˣ) (hu : (data ⟨j + 1, Nat.lt_succ_of_le hj⟩).b6 = π * ↑u)
local notation "Q" => Quotient R π m
local notation "A" => arithmeticFifthFartherAtlasObject hπ data H m j hj u hu
local notation "κ" => arithmeticFourthOuterAtlasChart hπ data H m j hj u hu

variable (ha : 3 = j)
local notation "E" => arithmeticFifthFartherAtlasCorrection hπ data H m j hj u hu ha
local notation "ι" => arithmeticFifthFartherAtlasChart hπ data H m j hj u hu ha
local notation "J" => arithmeticFourthOuterInitialThreeIdentification hπ data H m j hj u hu ha
local notation "C" => arithmeticFifthFartherIso hπ data H m j hj u hu
local notation "M" => arithmeticFourthFartherIdentification hπ data H m j hj u hu 0 ha
local notation "P" => arithmeticFifthFartherNeighborIso hπ data H m j hj u hu

/-- The corrected full initial open is exactly the installed depth-three label. -/
def arithmeticFifthFartherIdentification (_ha : 3 = j) (b : Bool) :
    arithmeticFifthFartherObject hπ data H m j hj u hu b ≅ A (.initial b) :=
  Iso.refl _

local notation "D" => arithmeticFifthFartherIdentification hπ data H m j hj u hu ha

omit [IsBezout R] in
/-- The installed initial factor starts from the actual fourth initial open. -/
theorem arithmeticFifthFartherAtlasCorrection_initial (b : Bool) :
    E (.initial b) = (J b).symm ≪≫ C b ≪≫ D b := by
  simp only [arithmeticFifthFartherAtlasCorrection, arithmeticFifthFartherIdentification,
    Iso.trans_refl]

/-- The installed initial comparison recovers the actual fourth inclusion. -/
@[reassoc] theorem arithmeticFifthFarther_chart (b : Bool) :
    (C b).hom ≫ (D b).hom ≫ ι (.initial b) = (J b).hom ≫ κ (.initial b) := by
  have h := arithmeticFifthFartherAtlasCorrection_chart hπ data H m j hj u hu ha (.initial b)
  rw [arithmeticFifthFartherAtlasCorrection_initial hπ data H m j hj u hu ha b] at h
  have hh := congrArg (fun f ↦ (J b).hom ≫ f) h
  simpa only [Iso.trans_hom, Iso.symm_hom, Category.assoc, Iso.hom_inv_id_assoc] using hh

/-- The first retained label has the specialized simultaneous fifth smoothing. -/
def arithmeticFifthFartherNeighborIdentification (b : Bool) :
    PolygonSmoothing.chart Q
        (arithmeticFifthFartherNeighborSmoothing hπ data H j hj u hu m b) ≅
      A (.retained ⟨0, by omega⟩ b) :=
  eqToIso (by simp only [arithmeticFifthFartherAtlasObject, ha.symm]; rfl)

local notation "F" => arithmeticFifthFartherNeighborIdentification hπ data H m j hj u hu ha

omit [IsBezout R] in
/-- The specialized neighbor replaces the generic factor from the same fourth source. -/
theorem arithmeticFifthFartherAtlasCorrection_neighbor (b : Bool) :
    E (.retained ⟨0, by omega⟩ b) = (M b).symm ≪≫ P b ≪≫ F b := by
  simp only [arithmeticFifthFartherAtlasCorrection, ha.symm,
    show ¬(0 : ℕ) = 3 by decide, show ¬(0 : ℕ) + 1 = 3 by decide,
    show ¬(0 : ℕ) + 2 = 3 by decide, show (0 : ℕ) + 3 = 3 by decide, ↓reduceDIte]
  rfl

/-- The neighbor's full comparison recovers its actual fourth inclusion. -/
@[reassoc] theorem arithmeticFifthFartherNeighbor_chart (b : Bool) :
    (P b).hom ≫ (F b).hom ≫ ι (.retained ⟨0, by omega⟩ b) =
      (M b).hom ≫ κ (.retained ⟨0, by omega⟩ b) := by
  have h := arithmeticFifthFartherAtlasCorrection_chart hπ data H m j hj u hu ha
    (.retained ⟨0, by omega⟩ b)
  rw [arithmeticFifthFartherAtlasCorrection_neighbor hπ data H m j hj u hu ha b] at h
  have hh := congrArg (fun f ↦ (M b).hom ≫ f) h
  simpa only [Iso.trans_hom, Iso.symm_hom, Category.assoc, Iso.hom_inv_id_assoc] using hh

end FLT.Mazur.WeierstrassDividedDepth
