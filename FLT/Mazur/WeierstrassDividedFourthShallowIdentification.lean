/-
Copyright (c) 2026 krandder. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: krandder
-/
module

public import FLT.Mazur.WeierstrassDividedFourthShallowAtlas
public import FLT.Mazur.WeierstrassDividedFourthAtlasIdentification

/-!
# Actual labels of the fourth depth-two initial atlas

The initial open and its neighbor are identified with their installed full
fourth objects. The last label keeps its already constructed fourth factor.
-/

@[expose] public noncomputable section
open AlgebraicGeometry CategoryTheory
namespace FLT.Mazur.WeierstrassDividedDepth
open PolygonArithmeticStages PolygonSmoothing WeierstrassModificationX
set_option backward.isDefEq.respectTransparency false
attribute [local irreducible] finiteGlobalModel finiteGlobalContraction
  arithmeticFourthShallowIso arithmeticFourthShallowNeighborIso arithmeticFourthOuterAtlasCorrection
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

variable (ha : 2 = j)
local notation "J" => arithmeticThirdShallowInitialIdentification hπ data H m j hj u hu ha
local notation "C" => arithmeticFourthShallowIso hπ data H m j hj u hu
local notation "M" => arithmeticThirdEarlierIdentification hπ data H m j hj u hu 0 ha
local notation "P" => arithmeticFourthShallowNeighborIso hπ data H m j hj u hu

/-- The corrected full initial open is exactly the installed depth-two label. -/
def arithmeticFourthShallowIdentification (b : Bool) :
    arithmeticFourthShallowObject hπ data H m j hj u hu b ≅ A (.initial b) :=
  eqToIso (by simp only [arithmeticFourthShallowAtlasObject, ha.symm, ↓reduceIte])

local notation "D" => arithmeticFourthShallowIdentification hπ data H m j hj u hu ha

omit [IsBezout R] in
/-- The installed initial factor starts from the actual third initial open. -/
theorem arithmeticFourthShallowAtlasCorrection_initial (b : Bool) :
    E (.initial b) = (J b).symm ≪≫ C b ≪≫ D b := by
  simp only [arithmeticFourthShallowAtlasCorrection, ha.symm, ↓reduceDIte]
  rfl

/-- The installed initial comparison recovers the actual third inclusion. -/
@[reassoc] theorem arithmeticFourthShallow_chart (b : Bool) :
    (C b).hom ≫ (D b).hom ≫ ι (.initial b) = (J b).hom ≫ κ (.initial b) := by
  have h := arithmeticFourthShallowAtlasCorrection_chart hπ data H m j hj u hu (.initial b)
  rw [arithmeticFourthShallowAtlasCorrection_initial hπ data H m j hj u hu ha b] at h
  have hh := congrArg (fun f ↦ (J b).hom ≫ f) h
  simpa only [Iso.trans_hom, Iso.symm_hom, Category.assoc, Iso.hom_inv_id_assoc] using hh

/-- The first retained label has the specialized simultaneous fourth smoothing. -/
def arithmeticFourthShallowNeighborIdentification (b : Bool) :
    PolygonSmoothing.chart Q
        (arithmeticFourthShallowNeighborSmoothing hπ data H j hj u hu m b) ≅
      A (.retained ⟨0, by omega⟩ b) :=
  eqToIso (by simp only [arithmeticFourthShallowAtlasObject, ha.symm, and_self, ↓reduceIte])

local notation "F" => arithmeticFourthShallowNeighborIdentification hπ data H m j hj u hu ha

omit [IsBezout R] in
/-- The specialized neighbor replaces the generic factor from the same third source. -/
theorem arithmeticFourthShallowAtlasCorrection_neighbor (b : Bool) :
    E (.retained ⟨0, by omega⟩ b) = (M b).symm ≪≫ P b ≪≫ F b := by
  simp only [arithmeticFourthShallowAtlasCorrection, ha.symm, and_self, ↓reduceDIte]
  rfl

/-- The neighbor's full comparison recovers its actual third inclusion. -/
@[reassoc] theorem arithmeticFourthShallowNeighbor_chart (b : Bool) :
    (P b).hom ≫ (F b).hom ≫ ι (.retained ⟨0, by omega⟩ b) =
      (M b).hom ≫ κ (.retained ⟨0, by omega⟩ b) := by
  have h := arithmeticFourthShallowAtlasCorrection_chart hπ data H m j hj u hu
    (.retained ⟨0, by omega⟩ b)
  rw [arithmeticFourthShallowAtlasCorrection_neighbor hπ data H m j hj u hu ha b] at h
  have hh := congrArg (fun f ↦ (M b).hom ≫ f) h
  simpa only [Iso.trans_hom, Iso.symm_hom, Category.assoc, Iso.hom_inv_id_assoc] using hh

end FLT.Mazur.WeierstrassDividedDepth
