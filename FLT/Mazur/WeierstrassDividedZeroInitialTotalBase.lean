/-
Copyright (c) 2026 krandder. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: krandder
-/
module

public import FLT.Mazur.WeierstrassDividedZeroDiagonalFactorRatio

/-!
# Every accumulated initial node correction preserves the coefficient base

Each full node factor is an algebra equivalence over the original quotient.
Composition and the final smoothing identification preserve that same base.
-/

@[expose] public noncomputable section
open AlgebraicGeometry CategoryTheory
namespace FLT.Mazur.WeierstrassDividedDepth
open PolygonArithmeticStages PolygonSmoothing WeierstrassModificationX
set_option backward.isDefEq.respectTransparency false
attribute [local irreducible] finiteGlobalModel finiteGlobalContraction
  arithmeticZeroFiniteInitialIso arithmeticInitialFactorRatioChart
/-- An algebra equivalence of whole node rings keeps their original coefficient projection. -/
@[reassoc] theorem nodeAlgebraIso_structure {K : Type} [CommRing K] {s t : K}
    (e : ChartRing t ≃ₐ[K] ChartRing s) :
    (Scheme.Spec.mapIso e.toRingEquiv.toCommRingCatIso.op).hom ≫
      PolygonSmoothing.chartStructure K t = PolygonSmoothing.chartStructure K s := by
  change Spec.map _ ≫ Spec.map _ = Spec.map _
  rw [← Spec.map_comp]
  congr 1
  exact CommRingCat.hom_ext (RingHom.ext e.commutes)

variable {R : Type} [CommRing R] [IsDomain R] {W : WeierstrassCurve R} {π : R}
  (hπ : π ≠ 0) {n : ℕ} (data : (i : Fin (n + 1)) → Data W π (1 + i.val))
  (H : ArithmeticAtlasCoefficients data) (m : ℕ) (hj : 1 ≤ n)
  (u : Rˣ) (hu : (data ⟨1, Nat.lt_succ_of_le hj⟩).b6 = π * ↑u)
local notation "Q" => Quotient R π m
local notation "τ" => arithmeticInitialMobiusSmoothing W H.a1_unit (π ^ 1) π m

/-- The first full node correction preserves its original quotient scalars. -/
@[reassoc] theorem arithmeticZeroFirstInitialNodeIso_base (b : Bool) :
    (arithmeticZeroFirstInitialNodeIso hπ data H m 0 hj u hu b).hom ≫
      PolygonSmoothing.chartStructure Q
        (arithmeticZeroFirstInitialSmoothing hπ data H 0 hj u hu m b) =
      PolygonSmoothing.chartStructure Q (τ) :=
  nodeAlgebraIso_structure _

/-- The second full node correction preserves its original quotient scalars. -/
@[reassoc] theorem arithmeticZeroSecondInitialNodeIso_base (b : Bool) :
    (arithmeticZeroSecondInitialNodeIso hπ data H m 0 hj u hu b).hom ≫
      PolygonSmoothing.chartStructure Q
        (arithmeticZeroSecondInitialSmoothing hπ data H 0 hj u hu m b) =
      PolygonSmoothing.chartStructure Q
        (arithmeticZeroFirstInitialSmoothing hπ data H 0 hj u hu m b) :=
  nodeAlgebraIso_structure _

/-- The third full node correction preserves its original quotient scalars. -/
@[reassoc] theorem arithmeticZeroThirdInitialNodeIso_base (b : Bool) :
    (arithmeticZeroThirdInitialNodeIso hπ data H m 0 hj u hu b).hom ≫
      PolygonSmoothing.chartStructure Q
        (arithmeticZeroThirdInitialSmoothing hπ data H 0 hj u hu m b) =
      PolygonSmoothing.chartStructure Q
        (arithmeticZeroSecondInitialSmoothing hπ data H 0 hj u hu m b) :=
  nodeAlgebraIso_structure _

/-- The fourth full node correction preserves its original quotient scalars. -/
@[reassoc] theorem arithmeticZeroFourthInitialNodeIso_base (b : Bool) :
    (arithmeticZeroFourthInitialNodeIso hπ data H m 0 hj u hu b).hom ≫
      PolygonSmoothing.chartStructure Q
        (arithmeticZeroFourthInitialSmoothing hπ data H 0 hj u hu m b) =
      PolygonSmoothing.chartStructure Q
        (arithmeticZeroThirdInitialSmoothing hπ data H 0 hj u hu m b) :=
  nodeAlgebraIso_structure _

/-- The fifth full node correction preserves its original quotient scalars. -/
@[reassoc] theorem arithmeticZeroFifthInitialNodeIso_base (b : Bool) :
    (arithmeticZeroFifthInitialNodeIso hπ data H m 0 hj u hu b).hom ≫
      PolygonSmoothing.chartStructure Q
        (arithmeticZeroFifthInitialSmoothing hπ data H 0 hj u hu m b) =
      PolygonSmoothing.chartStructure Q
        (arithmeticZeroFourthInitialSmoothing hπ data H 0 hj u hu m b) :=
  nodeAlgebraIso_structure _

/-- The entire finite node factor preserves the fifth node's original quotient scalars. -/
@[reassoc] theorem arithmeticZeroFiniteInitialNodeIso_base (k : ℕ) (b : Bool) :
    (arithmeticZeroFiniteInitialNodeIso hπ data H k m 0 hj u hu b).hom ≫
      PolygonSmoothing.chartStructure Q
        ((arithmeticZeroFiniteState hπ data H 0 hj u hu k).initial m b) =
      PolygonSmoothing.chartStructure Q
        (arithmeticZeroFifthInitialSmoothing hπ data H 0 hj u hu m b) :=
  nodeAlgebraIso_structure _

/-- All accumulated node corrections keep the complete original coefficient base. -/
@[reassoc] theorem arithmeticZeroDiagonalInitialTotalNodeIso_base (b : Bool) :
    (arithmeticZeroDiagonalInitialTotalNodeIso hπ data H m hj u hu b).hom ≫
      PolygonSmoothing.chartStructure Q
        ((arithmeticZeroDiagonalState hπ data H 0 hj u hu).initial m b) =
      PolygonSmoothing.chartStructure Q τ := by
  simp only [arithmeticZeroDiagonalInitialTotalNodeIso, Iso.trans_hom,
    nodeParameterIso, eqToIso_refl, Iso.refl_hom, Category.comp_id,
    arithmeticZeroFiniteInitialTotalNodeIso,
    arithmeticZeroFifthInitialTotalNodeIso, arithmeticZeroFourthInitialTotalNodeIso,
    arithmeticZeroThirdInitialTotalNodeIso, arithmeticZeroSecondInitialTotalNodeIso,
    Category.assoc, arithmeticZeroDiagonalState_initial, arithmeticZeroFiniteInitialNodeIso_base,
    arithmeticZeroFifthInitialNodeIso_base, arithmeticZeroFourthInitialNodeIso_base,
    arithmeticZeroThirdInitialNodeIso_base, arithmeticZeroSecondInitialNodeIso_base,
    arithmeticZeroFirstInitialNodeIso_base]

end FLT.Mazur.WeierstrassDividedDepth
