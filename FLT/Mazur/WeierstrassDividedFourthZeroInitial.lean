/-
Copyright (c) 2026 krandder. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: krandder
-/
module

public import FLT.Mazur.WeierstrassDividedFourthOuterAtlasClosing
public import FLT.Mazur.WeierstrassDividedThirdEarlierInitial

/-!
# The original initial source at depth zero

The first retained node is also the last node. The original initial open
keeps its full source and inclusion through the installed fourth atlas.
-/

@[expose] public noncomputable section
open AlgebraicGeometry CategoryTheory
namespace FLT.Mazur.WeierstrassDividedDepth
open PolygonArithmeticStages PolygonSmoothing WeierstrassModificationX
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
attribute [local irreducible] finiteGlobalModel finiteGlobalContraction
  arithmeticFourthOuterAtlasChart arithmeticFourthOuterIso
  arithmeticThirdAtlasChart arithmeticThirdInitialAtlasChart
variable {R : Type} [CommRing R] [IsDomain R] [IsBezout R]
  {W : WeierstrassCurve R} {π : R} (hπ : π ≠ 0) {n : ℕ}
  (data : (i : Fin (n + 1)) → Data W π (1 + i.val))
  (H : ArithmeticAtlasCoefficients data) (m j : ℕ) (hj : j + 1 ≤ n)
  (u : Rˣ) (hu : (data ⟨j + 1, Nat.lt_succ_of_le hj⟩).b6 = π * ↑u)
local notation "ι" => arithmeticThirdAtlasChart hπ data H m j hj u hu

variable (ha : 0 = j)
local notation "ω" => arithmeticFourthOuterAtlasChart hπ data H m j hj u hu

/-- At depth zero the installed initial label is the full original initial open. -/
def arithmeticFourthOuterInitialZeroIdentification (b : Bool) :
    arithmeticThirdAtlasObject hπ data H m j hj u hu (.initial b) ≅
      arithmeticFourthOuterAtlasObject hπ data H m j hj u hu (.initial b) :=
  eqToIso (by simp only [arithmeticFourthOuterAtlasObject, arithmeticFourthInitialAtlasObject,
    show ¬j = 1 by omega, ↓reduceIte, arithmeticFourthAtlasObject,
    arithmeticThirdInitialAtlasObject])

local notation "J" => arithmeticFourthOuterInitialZeroIdentification hπ data H m j hj u hu ha

/-- The identification retains the original full initial inclusion at depth zero. -/
@[reassoc] theorem arithmeticFourthOuterAtlasChart_initial_zero (b : Bool) :
    (J b).hom ≫ ω (.initial b) = ι (.initial b) := by
  have h := arithmeticFourthOuterAtlasCorrection_chart hπ data H m j hj u hu (.initial b)
  have hh := congrArg (fun f ↦
    (arithmeticThirdInitialAtlasCorrection hπ data H m j hj u hu (.initial b)).hom ≫ f) h
  rw [arithmeticThirdInitialAtlasCorrection_chart] at hh
  simpa only [arithmeticFourthOuterAtlasCorrection, arithmeticFourthInitialAtlasCorrection,
    arithmeticThirdInitialAtlasCorrection, show ¬j = 1 by omega, ↓reduceDIte,
    arithmeticFourthAtlasCorrection, arithmeticFourthOuterInitialZeroIdentification,
    Iso.trans_hom, Iso.refl_hom, Category.id_comp, eqToIso.hom,
    ← Category.assoc, eqToHom_trans] using hh

end FLT.Mazur.WeierstrassDividedDepth
