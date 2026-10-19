/-
Copyright (c) 2026 krandder. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: krandder
-/
module

public import FLT.Mazur.WeierstrassDividedOneInitialTotalTransport

/-!
# The full depth-one initial transport is the actual original atlas comparison

The constructed whole-open composite equals the installed original chart
isomorphism. Its entire node square therefore belongs to the actual source atlas.
-/

@[expose] public noncomputable section
open AlgebraicGeometry CategoryTheory
namespace FLT.Mazur.WeierstrassDividedDepth
open PolygonArithmeticStages PolygonSmoothing WeierstrassModificationX
set_option backward.isDefEq.respectTransparency false
attribute [local irreducible] arithmeticThirdInitialIso arithmeticFourthInitialIso
  arithmeticFifthInitialIso arithmeticOneFiniteInitialIso
variable {R : Type} [CommRing R] [IsDomain R] [IsBezout R]
  {W : WeierstrassCurve R} {π : R} (hπ : π ≠ 0) {n : ℕ}
  (data : (i : Fin (n + 1)) → Data W π (1 + i.val))
  (H : ArithmeticAtlasCoefficients data) (m : ℕ) (hj : 2 ≤ n)
  (u : Rˣ) (hu : (data ⟨2, Nat.lt_succ_of_le hj⟩).b6 = π * ↑u)
local notation "Q" => Quotient R π m
local notation "τ" => arithmeticInitialMobiusSmoothing W H.a1_unit (π ^ 1) π m
local notation "M" => arithmeticInitialMobiusChart W H.a1_unit (π ^ 1) π m

omit [IsBezout R] in
/-- The full original initial-open composite is precisely the installed atlas comparison. -/
theorem arithmeticOneFiniteInitialTotalOpenIso_atlas (k : ℕ) (b : Bool) :
    (arithmeticOneFiniteInitialTotalOpenIso hπ data H m hj u hu k b).hom =
      (arithmeticOneFiniteAtlasIso hπ data H k m hj u hu (.initial b)).hom := by
  simp only [arithmeticOneFiniteInitialTotalOpenIso, arithmeticOneFiniteAtlasIso,
    arithmeticOneFiniteAtlasCorrection, arithmeticFifthInitialAtlasIso,
    arithmeticFifthInitialAtlasCorrection, arithmeticFourthInitialAtlasIso,
    arithmeticFourthInitialAtlasCorrection, arithmeticThirdInitialAtlasIso,
    arithmeticThirdInitialAtlasCorrection, arithmeticThirdAtlasIso,
    arithmeticThirdAtlasCorrection, arithmeticSecondJointAtlasIso,
    arithmeticSecondJointAtlasCorrection, arithmeticResidualLiftAtlasIso,
    arithmeticResidualLiftAtlasCorrection, changedArithmeticAtlasIso,
    changedArithmeticAtlasToTwisted, twistedArithmeticAtlasIso,
    arithmeticThirdInitialIdentification, arithmeticFourthInitialIdentification,
    ↓reduceDIte, Iso.trans_hom, Iso.symm_hom, eqToIso_refl, Iso.refl_hom,
    Iso.refl_inv, Category.id_comp, Category.comp_id, Category.assoc]
  erw [Category.id_comp, Category.id_comp, Category.id_comp]

/-- The whole original initial open recovers its inclusion in the actual finite source. -/
@[reassoc] theorem arithmeticOneFiniteInitialTotalOpenIso_global (k : ℕ) (b : Bool) :
    (arithmeticOneFiniteInitialTotalOpenIso hπ data H m hj u hu k b).hom ≫
      arithmeticOneFiniteAtlasChart hπ data H k m hj u hu (.initial b) =
        arithmeticLabeledAtlasMap hπ data H m 2 hj (.initial b) ≫
          (simultaneousTwistedArithmeticIso hπ data H m 1 hj u hu).hom := by
  rw [arithmeticOneFiniteInitialTotalOpenIso_atlas]
  exact (arithmeticOneFiniteAtlasIso_chart hπ data H k m hj u hu (.initial b)).symm

omit [IsBezout R] in
/-- The installed initial node chart keeps the full original Mobius square. -/
@[reassoc] theorem arithmeticOneFiniteAtlasIso_initial_nodeChart (k : ℕ) (b : Bool) :
    (arithmeticOneFiniteAtlasIso hπ data H k m hj u hu (.initial b)).hom ≫
      arithmeticOneFiniteInitialNodeChart hπ data H k m hj u hu b =
        M ≫ (arithmeticOneFiniteInitialTotalNodeIso hπ data H m hj u hu k b).hom := by
  rw [← arithmeticOneFiniteInitialTotalOpenIso_atlas]
  exact arithmeticOneFiniteInitialTotalOpenIso_nodeChart hπ data H m hj u hu k b

/-- The actual diagonal inclusion retains both full original initial opens. -/
@[reassoc] theorem arithmeticOneDiagonalInitialTotalOpenIso_global (b : Bool) :
    (arithmeticOneDiagonalInitialTotalOpenIso hπ data H m hj u hu b).hom ≫
      arithmeticOneDiagonalAtlasChart hπ data H m hj u hu (.initial b) =
        arithmeticLabeledAtlasMap hπ data H m 2 hj (.initial b) ≫
          (simultaneousTwistedArithmeticIso hπ data H m 1 hj u hu).hom :=
  arithmeticOneFiniteInitialTotalOpenIso_global hπ data H m hj u hu m b

end FLT.Mazur.WeierstrassDividedDepth
