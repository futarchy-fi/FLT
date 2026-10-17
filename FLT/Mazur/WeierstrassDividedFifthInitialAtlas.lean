/-
Copyright (c) 2026 krandder. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: krandder
-/
module

public import FLT.Mazur.WeierstrassDividedFifthInitialGeometry
public import FLT.Mazur.WeierstrassDividedFifthInitialLastGeometry
public import FLT.Mazur.WeierstrassDividedFourthInitialAtlasClosing
public import FLT.Mazur.WeierstrassDividedFourthInitialAtlasSystem

/-!
# Simultaneous fifth factors on the entire depth-one atlas

Every retained label receives one whole-node factor, shared by both incident
edges. The initial open and terminal retain their complete fourth sources.
-/

@[expose] public noncomputable section
open AlgebraicGeometry CategoryTheory
namespace FLT.Mazur.WeierstrassDividedDepth
open PolygonArithmeticStages PolygonSmoothing WeierstrassModificationX
set_option backward.isDefEq.respectTransparency false
attribute [local irreducible] finiteGlobalModel finiteGlobalContraction
  arithmeticFourthInitialAtlasCorrection arithmeticFourthInitialAtlasChart
  arithmeticFifthInitialIso arithmeticFifthInitialNeighborIso
  arithmeticFifthInitialLastOrientedIso
  arithmeticFifthShallowTerminalIso
variable {R : Type} [CommRing R] [IsDomain R] [IsBezout R]
  {W : WeierstrassCurve R} {π : R} (hπ : π ≠ 0) {n : ℕ}
  (data : (i : Fin (n + 1)) → Data W π (1 + i.val))
  (H : ArithmeticAtlasCoefficients data) (m : ℕ) (hj : 2 ≤ n)
  (u : Rˣ) (hu : (data ⟨2, Nat.lt_succ_of_le hj⟩).b6 = π * ↑u)
local notation "Q" => Quotient R π m
local notation "τ" => arithmeticInitialMobiusSmoothing W H.a1_unit (π ^ 1) π m
local notation "B" => arithmeticFourthInitialAtlasObject hπ data H m 1 hj u hu
local notation "κ" => arithmeticFourthInitialAtlasChart hπ data H m 1 hj u hu
local notation "I" => arithmeticFourthInitialAtlasIso hπ data H m 1 hj u hu

/-- The fifth objects at each actual depth-one label, including the original infinity. -/
def arithmeticFifthInitialAtlasObject : ArithmeticChartLabel 2 → Scheme
  | .initial b => arithmeticFifthInitialObject hπ data H m 1 hj u hu b
  | .retained a b => match a.val with
    | 0 => PolygonSmoothing.chart Q
        (arithmeticFifthInitialNeighborSmoothing hπ data H 1 hj u hu m b)
    | _ => PolygonSmoothing.chart Q τ
  | .terminal => PolygonSmoothing.chart Q
      (arithmeticFifthShallowTerminalSmoothing hπ data H 1 hj u hu m)
  | .infinity => B .infinity

local notation "A" => arithmeticFifthInitialAtlasObject hπ data H m hj u hu

/-- All fifth factors are installed together from the same fourth atlas. -/
def arithmeticFifthInitialAtlasCorrection (i : ArithmeticChartLabel 2) : B i ≅ A i :=
  match i with
  | .initial b =>
    (arithmeticFourthInitialIdentification hπ data H m 1 hj u hu rfl b).symm ≪≫
      arithmeticFifthInitialIso hπ data H m 1 hj u hu b
  | .retained ⟨0, _⟩ b =>
    (arithmeticFourthInitialNeighborIdentification hπ data H m 1 hj u hu rfl b).symm ≪≫
      arithmeticFifthInitialNeighborIso hπ data H m 1 hj u hu b
  | .retained ⟨1, _⟩ b =>
    (arithmeticFourthInitialLastIdentification hπ data H m 1 hj u hu b).symm ≪≫
      arithmeticFifthInitialLastOrientedIso hπ data H m 1 hj u hu b
  | .retained ⟨k + 2, hk⟩ _ => False.elim (by omega)
  | .terminal => arithmeticFifthShallowTerminalIso hπ data H m 1 hj u hu
  | .infinity => Iso.refl _

attribute [local irreducible] arithmeticFifthInitialAtlasCorrection
local notation "E" => arithmeticFifthInitialAtlasCorrection hπ data H m hj u hu

/-- The full fifth chart inclusion in the unchanged global target. -/
def arithmeticFifthInitialAtlasChart (i : ArithmeticChartLabel 2) :
    A i ⟶ simultaneousTwistedArithmeticStage hπ data H m 1 hj u hu :=
  (E i).inv ≫ κ i

instance arithmeticFifthInitialAtlasChart_isOpenImmersion (i : ArithmeticChartLabel 2) :
    IsOpenImmersion (arithmeticFifthInitialAtlasChart hπ data H m hj u hu i) := by
  unfold arithmeticFifthInitialAtlasChart
  infer_instance

/-- The comparison from each original chart includes all five complete correction rounds. -/
def arithmeticFifthInitialAtlasIso (i : ArithmeticChartLabel 2) :
    arithmeticLabeledAtlasObject hπ data H m 2 hj i ≅ A i := I i ≪≫ E i

local notation "ι" => arithmeticFifthInitialAtlasChart hπ data H m hj u hu

/-- The installed correction recovers the exact fourth inclusion at every label. -/
@[reassoc] theorem arithmeticFifthInitialAtlasCorrection_chart (i : ArithmeticChartLabel 2) :
    (E i).hom ≫ ι i = κ i := by
  rw [arithmeticFifthInitialAtlasChart, Iso.hom_inv_id_assoc]

/-- The original global inclusion is recovered by the composed full chart comparison. -/
@[reassoc] theorem arithmeticFifthInitialAtlasIso_chart (i : ArithmeticChartLabel 2) :
    arithmeticLabeledAtlasMap hπ data H m 2 hj i ≫
        (simultaneousTwistedArithmeticIso hπ data H m 1 hj u hu).hom =
      (arithmeticFifthInitialAtlasIso hπ data H m hj u hu i).hom ≫ ι i := by
  rw [arithmeticFifthInitialAtlasIso, Iso.trans_hom, Category.assoc,
    arithmeticFifthInitialAtlasCorrection_chart]
  exact arithmeticFourthInitialAtlasIso_chart hπ data H m 1 hj u hu i

attribute [local irreducible] arithmeticFifthInitialAtlasChart

/-- The simultaneous fifth factors transport the entire original cover. -/
def arithmeticFifthInitialOpenCover :
    (simultaneousTwistedArithmeticStage hπ data H m 1 hj u hu).OpenCover :=
  (arithmeticFourthInitialOpenCover hπ data H m 1 hj u hu).copy
    (ArithmeticChartLabel 2) A ι (Equiv.refl _) (fun i ↦ (E i).symm)
      (fun _ ↦ by rw [arithmeticFifthInitialAtlasChart]; rfl)

/-- Every point of the full global target remains covered by a fifth chart. -/
theorem arithmeticFifthInitialAtlas_cover
    (z : simultaneousTwistedArithmeticStage hπ data H m 1 hj u hu) :
    ∃ i x, ι i x = z := (arithmeticFifthInitialOpenCover hπ data H m hj u hu).exists_eq z

end FLT.Mazur.WeierstrassDividedDepth
