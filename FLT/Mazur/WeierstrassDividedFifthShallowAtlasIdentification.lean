/-
Copyright (c) 2026 krandder. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: krandder
-/
module

public import FLT.Mazur.WeierstrassDividedFifthShallowAtlas

/-!
# Concrete global chart comparisons for the fifth depth-two atlas

All three retained labels and both initial labels recover their exact fourth
inclusions through the installed whole-node factors. Infinity is unchanged.
-/

@[expose] public noncomputable section
open AlgebraicGeometry CategoryTheory
namespace FLT.Mazur.WeierstrassDividedDepth
open PolygonArithmeticStages PolygonSmoothing WeierstrassModificationX
set_option backward.isDefEq.respectTransparency false
attribute [local irreducible] finiteGlobalModel finiteGlobalContraction
  arithmeticFourthShallowAtlasChart arithmeticFifthShallowIso
  arithmeticFifthShallowNeighborIso arithmeticFifthShallowPrecedingIso
  arithmeticFifthShallowLastOrientedIso arithmeticFifthShallowTerminalIso
variable {R : Type} [CommRing R] [IsDomain R] [IsBezout R]
  {W : WeierstrassCurve R} {π : R} (hπ : π ≠ 0) {n : ℕ}
  (data : (i : Fin (n + 1)) → Data W π (1 + i.val))
  (H : ArithmeticAtlasCoefficients data) (m : ℕ) (hj : 3 ≤ n)
  (u : Rˣ) (hu : (data ⟨3, Nat.lt_succ_of_le hj⟩).b6 = π * ↑u)
local notation "ι" => arithmeticFifthShallowAtlasChart hπ data H m hj u hu
local notation "κ" => arithmeticFourthShallowAtlasChart hπ data H m 2 hj u hu

/-- The installed initial factor recovers its full fourth global chart. -/
@[reassoc] theorem arithmeticFifthShallowInitial_chart (b : Bool) :
    (arithmeticFifthShallowIso hπ data H m 2 hj u hu b).hom ≫ ι (.initial b) =
      (arithmeticFourthShallowIdentification hπ data H m 2 hj u hu rfl b).hom ≫ κ (.initial b) := by
  simp only [arithmeticFifthShallowAtlasChart, arithmeticFifthShallowAtlasCorrection,
    Iso.trans_inv, Iso.symm_inv, Category.assoc, Iso.hom_inv_id_assoc]

/-- The installed neighbor factor recovers its full fourth global chart. -/
@[reassoc] theorem arithmeticFifthShallowNeighbor_chart (b : Bool) :
    (arithmeticFifthShallowNeighborIso hπ data H m 2 hj u hu b).hom ≫
        ι (.retained ⟨0, by omega⟩ b) =
      (arithmeticFourthShallowNeighborIdentification hπ data H m 2 hj u hu rfl b).hom ≫
        κ (.retained ⟨0, by omega⟩ b) := by
  simp only [arithmeticFifthShallowAtlasChart, arithmeticFifthShallowAtlasCorrection,
    Iso.trans_inv, Iso.symm_inv, Category.assoc, Iso.hom_inv_id_assoc]

/-- The installed preceding factor recovers its full fourth global chart. -/
@[reassoc] theorem arithmeticFifthShallowPreceding_chart (b : Bool) :
    (arithmeticFifthShallowPrecedingIso hπ data H m 2 hj u hu b).hom ≫
        ι (.retained ⟨1, by omega⟩ b) =
      (arithmeticFourthShallowPrecedingIdentification
        hπ data H m 2 hj u hu 1 rfl (by omega) b).hom ≫ κ (.retained ⟨1, by omega⟩ b) := by
  simp only [arithmeticFifthShallowAtlasChart, arithmeticFifthShallowAtlasCorrection,
    Iso.trans_inv, Iso.symm_inv, Category.assoc, Iso.hom_inv_id_assoc]

/-- The installed last factor recovers its full fourth global chart. -/
@[reassoc] theorem arithmeticFifthShallowLast_chart (b : Bool) :
    (arithmeticFifthShallowLastOrientedIso hπ data H m 2 hj u hu b).hom ≫
        ι (.retained ⟨2, by omega⟩ b) =
      (arithmeticFourthShallowLastIdentification hπ data H m 2 hj u hu b).hom ≫
        κ (.retained ⟨2, by omega⟩ b) := by
  simp only [arithmeticFifthShallowAtlasChart, arithmeticFifthShallowAtlasCorrection,
    Iso.trans_inv, Iso.symm_inv, Category.assoc, Iso.hom_inv_id_assoc]

/-- The complete terminal factor recovers the same fourth terminal inclusion. -/
@[reassoc] theorem arithmeticFifthShallowTerminal_chart :
    (arithmeticFifthShallowTerminalIso hπ data H m 2 hj u hu).hom ≫ ι .terminal =
      κ .terminal := by
  simp only [arithmeticFifthShallowAtlasChart, arithmeticFifthShallowAtlasCorrection,
    Iso.hom_inv_id_assoc]

/-- The fifth atlas leaves the infinity chart and its inclusion unchanged. -/
theorem arithmeticFifthShallowAtlasChart_infinity : ι .infinity = κ .infinity := by
  simp only [arithmeticFifthShallowAtlasChart, arithmeticFifthShallowAtlasCorrection,
    Iso.refl_inv]
  exact Category.id_comp _

end FLT.Mazur.WeierstrassDividedDepth
