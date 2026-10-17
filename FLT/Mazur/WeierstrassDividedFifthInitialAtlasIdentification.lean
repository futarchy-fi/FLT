/-
Copyright (c) 2026 krandder. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: krandder
-/
module

public import FLT.Mazur.WeierstrassDividedFifthInitialAtlas

/-!
# Concrete global chart comparisons for the fifth depth-one atlas

Both retained labels and both initial labels recover their exact fourth
inclusions through the installed whole-node factors. Infinity is unchanged.
-/

@[expose] public noncomputable section
open AlgebraicGeometry CategoryTheory
namespace FLT.Mazur.WeierstrassDividedDepth
open PolygonArithmeticStages PolygonSmoothing WeierstrassModificationX
set_option backward.isDefEq.respectTransparency false
attribute [local irreducible] finiteGlobalModel finiteGlobalContraction
  arithmeticFourthInitialAtlasChart arithmeticFifthInitialIso
  arithmeticFifthInitialNeighborIso
  arithmeticFifthInitialLastOrientedIso arithmeticFifthShallowTerminalIso
variable {R : Type} [CommRing R] [IsDomain R] [IsBezout R]
  {W : WeierstrassCurve R} {π : R} (hπ : π ≠ 0) {n : ℕ}
  (data : (i : Fin (n + 1)) → Data W π (1 + i.val))
  (H : ArithmeticAtlasCoefficients data) (m : ℕ) (hj : 2 ≤ n)
  (u : Rˣ) (hu : (data ⟨2, Nat.lt_succ_of_le hj⟩).b6 = π * ↑u)
local notation "ι" => arithmeticFifthInitialAtlasChart hπ data H m hj u hu
local notation "κ" => arithmeticFourthInitialAtlasChart hπ data H m 1 hj u hu

/-- The installed initial factor recovers its full fourth global chart. -/
@[reassoc] theorem arithmeticFifthInitialInitial_chart (b : Bool) :
    (arithmeticFifthInitialIso hπ data H m 1 hj u hu b).hom ≫ ι (.initial b) =
      (arithmeticFourthInitialIdentification hπ data H m 1 hj u hu rfl b).hom ≫ κ (.initial b) := by
  simp only [arithmeticFifthInitialAtlasChart, arithmeticFifthInitialAtlasCorrection,
    Iso.trans_inv, Iso.symm_inv, Category.assoc, Iso.hom_inv_id_assoc]

/-- The installed neighbor factor recovers its full fourth global chart. -/
@[reassoc] theorem arithmeticFifthInitialNeighbor_chart (b : Bool) :
    (arithmeticFifthInitialNeighborIso hπ data H m 1 hj u hu b).hom ≫
        ι (.retained ⟨0, by omega⟩ b) =
      (arithmeticFourthInitialNeighborIdentification hπ data H m 1 hj u hu rfl b).hom ≫
        κ (.retained ⟨0, by omega⟩ b) := by
  simp only [arithmeticFifthInitialAtlasChart, arithmeticFifthInitialAtlasCorrection,
    Iso.trans_inv, Iso.symm_inv, Category.assoc, Iso.hom_inv_id_assoc]

/-- The installed last factor recovers its full fourth global chart. -/
@[reassoc] theorem arithmeticFifthInitialLast_chart (b : Bool) :
    (arithmeticFifthInitialLastOrientedIso hπ data H m 1 hj u hu b).hom ≫
        ι (.retained ⟨1, by omega⟩ b) =
      (arithmeticFourthInitialLastIdentification hπ data H m 1 hj u hu b).hom ≫
        κ (.retained ⟨1, by omega⟩ b) := by
  simp only [arithmeticFifthInitialAtlasChart, arithmeticFifthInitialAtlasCorrection,
    Iso.trans_inv, Iso.symm_inv, Category.assoc, Iso.hom_inv_id_assoc]

/-- The complete terminal factor recovers the same fourth terminal inclusion. -/
@[reassoc] theorem arithmeticFifthInitialTerminal_chart :
    (arithmeticFifthShallowTerminalIso hπ data H m 1 hj u hu).hom ≫ ι .terminal =
      κ .terminal := by
  simp only [arithmeticFifthInitialAtlasChart, arithmeticFifthInitialAtlasCorrection,
    Iso.hom_inv_id_assoc]

/-- The fifth atlas leaves the infinity chart and its inclusion unchanged. -/
theorem arithmeticFifthInitialAtlasChart_infinity : ι .infinity = κ .infinity := by
  simp only [arithmeticFifthInitialAtlasChart, arithmeticFifthInitialAtlasCorrection,
    Iso.refl_inv]
  exact Category.id_comp _

end FLT.Mazur.WeierstrassDividedDepth
