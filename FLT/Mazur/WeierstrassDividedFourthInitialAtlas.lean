/-
Copyright (c) 2026 krandder. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: krandder
-/
module

public import FLT.Mazur.WeierstrassDividedFourthAtlas
public import FLT.Mazur.WeierstrassDividedFourthInitialGeometry
public import FLT.Mazur.WeierstrassDividedThirdInitialAtlasEdge

/-!
# Install the dedicated fourth depth-one initial factors

Both specialized factors start from the third atlas. All other labels keep
exactly their fourth corrections, including the terminal and original infinity.
-/

@[expose] public noncomputable section
open AlgebraicGeometry CategoryTheory
namespace FLT.Mazur.WeierstrassDividedDepth
open PolygonArithmeticStages PolygonSmoothing WeierstrassModificationX
set_option backward.isDefEq.respectTransparency false
attribute [local irreducible] finiteGlobalModel finiteGlobalContraction
  arithmeticFourthInitialIso arithmeticFourthInitialNeighborIso
  arithmeticFourthAtlasCorrection
variable {R : Type} [CommRing R] [IsDomain R] [IsBezout R]
  {W : WeierstrassCurve R} {π : R} (hπ : π ≠ 0) {n : ℕ}
  (data : (i : Fin (n + 1)) → Data W π (1 + i.val))
  (H : ArithmeticAtlasCoefficients data) (m j : ℕ) (hj : j + 1 ≤ n)
  (u : Rˣ) (hu : (data ⟨j + 1, Nat.lt_succ_of_le hj⟩).b6 = π * ↑u)
local notation "Q" => Quotient R π m
local notation "τ" => arithmeticInitialMobiusSmoothing W H.a1_unit (π ^ 1) π m
local notation "B" => arithmeticThirdInitialAtlasObject hπ data H m j hj u hu
local notation "κ" => arithmeticThirdInitialAtlasChart hπ data H m j hj u hu
local notation "I" => arithmeticThirdInitialAtlasIso hπ data H m j hj u hu
local notation "G" => simultaneousTwistedArithmeticIso hπ data H m j hj u hu

/-- Replace only the depth-one initial open and its actual retained neighbor. -/
def arithmeticFourthInitialAtlasObject : ArithmeticChartLabel (j + 1) → Scheme
  | .initial b => if j = 1 then arithmeticFourthInitialObject hπ data H m j hj u hu b
      else arithmeticFourthAtlasObject hπ data H m j hj u hu (.initial b)
  | .retained a b => if j = 1 ∧ a.val = 0 then PolygonSmoothing.chart Q
      (arithmeticFourthInitialNeighborSmoothing hπ data H j hj u hu m b)
      else arithmeticFourthAtlasObject hπ data H m j hj u hu (.retained a b)
  | i => arithmeticFourthAtlasObject hπ data H m j hj u hu i

local notation "A" => arithmeticFourthInitialAtlasObject hπ data H m j hj u hu
local notation "E₄" => arithmeticFourthAtlasCorrection hπ data H m j hj u hu

/-- Install both new factors from their third sources, retaining the other fourth factors. -/
def arithmeticFourthInitialAtlasCorrection (i : ArithmeticChartLabel (j + 1)) : B i ≅ A i :=
  match i with
  | .initial b => if h : j = 1 then
      (arithmeticThirdInitialIdentification hπ data H m j hj u hu h.symm b).symm ≪≫
        arithmeticFourthInitialIso hπ data H m j hj u hu b ≪≫
          eqToIso (by simp only [arithmeticFourthInitialAtlasObject, h, ↓reduceIte])
      else E₄ (.initial b) ≪≫
        eqToIso (by simp only [arithmeticFourthInitialAtlasObject, h, ↓reduceIte])
  | .retained a b => if h : j = 1 ∧ a.val = 0 then
      (arithmeticThirdPrecedingIdentification
        hπ data H m j hj u hu a.val (by omega) b).symm ≪≫
        arithmeticFourthInitialNeighborIso hπ data H m j hj u hu b ≪≫
          eqToIso (by simp only [arithmeticFourthInitialAtlasObject, ite_eq_left h])
      else E₄ (.retained a b) ≪≫
        eqToIso (by simp only [arithmeticFourthInitialAtlasObject, h, ↓reduceIte])
  | .terminal => E₄ .terminal
  | .infinity => E₄ .infinity

attribute [local irreducible] arithmeticFourthInitialAtlasCorrection
local notation "E" => arithmeticFourthInitialAtlasCorrection hπ data H m j hj u hu

/-- The actual corrected full chart inclusion in the global target. -/
def arithmeticFourthInitialAtlasChart (i : ArithmeticChartLabel (j + 1)) :
    A i ⟶ simultaneousTwistedArithmeticStage hπ data H m j hj u hu :=
  (E i).inv ≫ κ i

instance arithmeticFourthInitialAtlasChart_isOpenImmersion (i : ArithmeticChartLabel (j + 1)) :
    IsOpenImmersion (arithmeticFourthInitialAtlasChart hπ data H m j hj u hu i) := by
  unfold arithmeticFourthInitialAtlasChart
  infer_instance

/-- Every original full chart has its composed four-round depth-one comparison. -/
def arithmeticFourthInitialAtlasIso (i : ArithmeticChartLabel (j + 1)) :
    arithmeticLabeledAtlasObject hπ data H m (j + 1) hj i ≅ A i := I i ≪≫ E i

local notation "ι" => arithmeticFourthInitialAtlasChart hπ data H m j hj u hu

/-- The correction recovers its actual third-atlas inclusion. -/
@[reassoc] theorem arithmeticFourthInitialAtlasCorrection_chart (i : ArithmeticChartLabel (j + 1)) :
    (E i).hom ≫ ι i = κ i := by
  rw [arithmeticFourthInitialAtlasChart, Iso.hom_inv_id_assoc]

/-- The original full chart inclusion is recovered by the four constructed comparisons. -/
@[reassoc] theorem arithmeticFourthInitialAtlasIso_chart (i : ArithmeticChartLabel (j + 1)) :
    arithmeticLabeledAtlasMap hπ data H m (j + 1) hj i ≫ (G).hom =
      (arithmeticFourthInitialAtlasIso hπ data H m j hj u hu i).hom ≫ ι i := by
  rw [arithmeticFourthInitialAtlasIso, Iso.trans_hom, Category.assoc,
    arithmeticFourthInitialAtlasCorrection_chart]
  exact arithmeticThirdInitialAtlasIso_chart hπ data H m j hj u hu i

attribute [local irreducible] arithmeticFourthInitialAtlasChart arithmeticThirdInitialAtlasChart

/-- Transport the complete original cover through the full fourth depth-one factors. -/
def arithmeticFourthInitialOpenCover :
    (simultaneousTwistedArithmeticStage hπ data H m j hj u hu).OpenCover :=
  (arithmeticThirdInitialOpenCover hπ data H m j hj u hu).copy
    (ArithmeticChartLabel (j + 1)) A ι (Equiv.refl _) (fun i ↦ (E i).symm)
      (fun _ ↦ by rw [arithmeticFourthInitialAtlasChart]; rfl)

/-- The installed fourth charts cover the entire target, including its original infinity. -/
theorem arithmeticFourthInitialAtlas_cover
    (z : simultaneousTwistedArithmeticStage hπ data H m j hj u hu) :
    ∃ i x, ι i x = z := (arithmeticFourthInitialOpenCover hπ data H m j hj u hu).exists_eq z

end FLT.Mazur.WeierstrassDividedDepth
