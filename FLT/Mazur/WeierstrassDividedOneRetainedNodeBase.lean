/-
Copyright (c) 2026 krandder. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: krandder
-/
module

public import FLT.Mazur.WeierstrassDividedOneInfinityNormalizedFullUnion
public import FLT.Mazur.WeierstrassDividedRevisedInitialBase
public import FLT.Mazur.WeierstrassDividedFourthClosingFactorBase

/-!
# Coefficient bases of the complete depth-one retained-0 corrections

Every whole-node correction preserves the original quotient coefficients,
including the removed original orientation and the varying finite factor.
-/

@[expose] public noncomputable section
open scoped LaurentPolynomial
open AlgebraicGeometry CategoryTheory
namespace FLT.Mazur.WeierstrassDividedDepth
open PolygonArithmeticStages PolygonSmoothing WeierstrassModificationX
open WeierstrassIntegralChart
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
attribute [local irreducible] finiteGlobalModel finiteGlobalContraction
  arithmeticOneFiniteInitialIso arithmeticInitialFactorRatioChart arithmeticOneFiniteAtlasIso
  simultaneousTwistedArithmeticIso arithmeticLabeledAtlasMap
variable {R : Type} [CommRing R] [IsDomain R]
  {W : WeierstrassCurve R} {π : R} (hπ : π ≠ 0) {n : ℕ}
  (data : (i : Fin (n + 1)) → Data W π (1 + i.val))
  (H : ArithmeticAtlasCoefficients data) (m : ℕ) (hj : 2 ≤ n)
  (u : Rˣ) (hu : (data ⟨2, Nat.lt_succ_of_le hj⟩).b6 = π * ↑u)
local notation "Q" => Quotient R π m
local notation "τ" => arithmeticInitialMobiusSmoothing W H.a1_unit (π ^ 1) π m
/-- The full second predecessor factor is defined over the original quotient coefficients. -/
@[reassoc] theorem arithmeticOneSecondPrecedingIso_base (b : Bool) :
    (arithmeticSecondPrecedingIso hπ data H m 1 hj u hu b).hom ≫
      chartStructure Q (arithmeticSecondPrecedingSmoothing hπ data H m 1 hj u hu b) =
        chartStructure Q τ := nodeAlgebraIso_structure _

/-- Removing the original orientation still preserves the entire coefficient base. -/
@[reassoc] theorem arithmeticOneSecondPrecedingOrientedIso_base (b : Bool) :
    (arithmeticSecondPrecedingOrientedIso hπ data H m 1 hj u hu b).hom ≫
      chartStructure Q (arithmeticSecondPrecedingSmoothing hπ data H m 1 hj u hu b) =
        chartStructure Q τ := by
  simp only [arithmeticSecondPrecedingOrientedIso, Iso.trans_hom, Iso.symm_hom,
    Category.assoc, arithmeticOneSecondPrecedingIso_base]
  apply (cancel_epi (twistedRetainedOrientation data H m b).hom).mp
  rw [Iso.hom_inv_id_assoc, twistedRetainedOrientation_base]

/-- The full third predecessor factor preserves its exact old and new coefficient maps. -/
@[reassoc] theorem arithmeticOneThirdPrecedingIso_base (b : Bool) :
    (arithmeticThirdPrecedingIso hπ data H m 1 hj u hu b).hom ≫
      chartStructure Q (arithmeticThirdPrecedingSmoothing hπ data H 1 hj u hu m b) =
        chartStructure Q (arithmeticSecondPrecedingSmoothing hπ data H m 1 hj u hu b) :=
  nodeAlgebraIso_structure _

/-- The entire fourth retained-0 factor preserves its original quotient scalars. -/
@[reassoc] theorem arithmeticOneFourthNeighborIso_base (b : Bool) :
    (arithmeticFourthInitialNeighborIso hπ data H m 1 hj u hu b).hom ≫
      chartStructure Q (arithmeticFourthInitialNeighborSmoothing hπ data H 1 hj u hu m b) =
        chartStructure Q (arithmeticThirdPrecedingSmoothing hπ data H 1 hj u hu m b) :=
  nodeAlgebraIso_structure _

/-- The entire fifth retained-0 factor preserves its original quotient scalars. -/
@[reassoc] theorem arithmeticOneFifthNeighborIso_base (b : Bool) :
    (arithmeticFifthInitialNeighborIso hπ data H m 1 hj u hu b).hom ≫
      chartStructure Q (arithmeticFifthInitialNeighborSmoothing hπ data H 1 hj u hu m b) =
        chartStructure Q (arithmeticFourthInitialNeighborSmoothing hπ data H 1 hj u hu m b) :=
  nodeAlgebraIso_structure _

/-- Each full finite retained-node factor preserves the original coefficient projection. -/
@[reassoc] theorem arithmeticOneFiniteRetainedIso_base (k : ℕ) (i : Fin 2) (b : Bool) :
    (arithmeticOneFiniteRetainedIso hπ data H k m hj u hu i b).hom ≫
      chartStructure Q ((arithmeticOneFiniteState hπ data H hj u hu k).retained m i b) =
        chartStructure Q ((arithmeticOneSeedState hπ data H hj u hu).retained m i b) :=
  nodeAlgebraIso_structure _

end FLT.Mazur.WeierstrassDividedDepth
