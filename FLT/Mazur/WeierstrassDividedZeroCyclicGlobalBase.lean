/-
Copyright (c) 2026 krandder. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: krandder
-/
module

public import FLT.Mazur.WeierstrassDividedZeroCyclicGlobalIso
public import FLT.Mazur.WeierstrassDividedZeroCyclicSourceBase

/-!
# The standard five-gon comparison over the original arithmetic base

The global comparison preserves the coefficient map on every full node,
and hence defines an isomorphism in the category over the quotient base.
-/

@[expose] public noncomputable section
open AlgebraicGeometry CategoryTheory
namespace FLT.Mazur.WeierstrassDividedDepth
open PolygonArithmeticStages PolygonSmoothing
set_option backward.isDefEq.respectTransparency false
variable {R : Type} [CommRing R] [IsDomain R] [IsBezout R]
  {W : WeierstrassCurve R} {π : R} (hπ : π ≠ 0) {n : ℕ}
  (data : (i : Fin (n + 1)) → Data W π (1 + i.val))
  (H : ArithmeticAtlasCoefficients data) (m : ℕ) (hj : 1 ≤ n)
  (u : Rˣ) (hu : (data ⟨1, Nat.lt_succ_of_le hj⟩).b6 = π * ↑u)
local notation "Q" => Quotient R π m
local notation "t" => arithmeticZeroCyclicStandardParameter hπ data H hj u hu m
local notation "G" => arithmeticZeroCyclicGlobalMap hπ data H m hj u hu
local notation "I" => arithmeticZeroCyclicInverseMap hπ data H m hj u hu
local notation "X" => simultaneousTwistedArithmeticStage hπ data H m 0 hj u hu
local notation "Y" => arithmeticZeroCyclicStandard hπ data H hj u hu m

local notation "q" => arithmeticZeroDiagonalSourceToBase hπ data H m hj u hu

/-- The independently glued standard target has its original coefficient projection. -/
def arithmeticZeroCyclicStandardToBase : Y ⟶ Spec (.of Q) :=
  PolygonVariableSmoothing.toBase Q 5 t (by decide)

local notation "p" => arithmeticZeroCyclicStandardToBase hπ data H m hj u hu

/-- Every whole standard chart preserves the original quotient coefficients. -/
@[reassoc] theorem arithmeticZeroCyclicStandardChart_base (i : Fin 5) :
    arithmeticZeroCyclicStandardChart hπ data H hj u hu m i ≫ p =
      chartStructure Q (t i) :=
  PolygonVariableSmoothing.chart_toBase Q 5 t (by decide) i

/-- The entire constructed global isomorphism preserves the actual source base. -/
@[reassoc] theorem arithmeticZeroCyclicGlobalIso_base :
    (arithmeticZeroCyclicGlobalIso hπ data H m hj u hu).hom ≫ p = q := by
  apply arithmeticZeroCyclicSourceChart_hom_ext hπ data H m hj u hu
  intro i
  obtain ⟨j, rfl⟩ := zeroCyclicIndex.surjective i
  rw [arithmeticZeroCyclicGlobalIso_chart_assoc, arithmeticZeroCyclicStandardChart_base]
  dsimp only [arithmeticZeroCyclicStandardParameter]
  rw [arithmeticZeroCyclicNodeIso_base, arithmeticZeroCyclicSourceChart_base]

/-- The actual original stage and the independent standard five-gon are isomorphic over base. -/
def arithmeticZeroCyclicGlobalOverIso : Over.mk q ≅ Over.mk p :=
  Over.isoMk (arithmeticZeroCyclicGlobalIso hπ data H m hj u hu)
    (arithmeticZeroCyclicGlobalIso_base hπ data H m hj u hu)

/-- The independent target quotient retains the original base restriction. -/
@[reassoc] theorem arithmeticZeroCyclicStandardRestriction_base :
    arithmeticZeroCyclicStandardRestriction hπ data H hj u hu m ≫
      arithmeticZeroCyclicStandardToBase hπ data H (m + 1) hj u hu =
        p ≫ baseRestriction R π m :=
  PolygonVariableSmoothing.parameterProjection_base (restriction R π m).toRingHom 5
    (arithmeticZeroCyclicStandardParameter hπ data H hj u hu (m + 1)) t
    (fun i ↦ (arithmeticZeroCyclicDiagonal_compatible hπ data H hj u hu).1 m
      (zeroCyclicIndex i)) (by decide)

end FLT.Mazur.WeierstrassDividedDepth
