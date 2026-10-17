/-
Copyright (c) 2026 krandder. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: krandder
-/
module

public import FLT.Mazur.WeierstrassDividedFifthShallowGeometry
public import FLT.Mazur.WeierstrassDividedFifthShallowJointGeometry
public import FLT.Mazur.WeierstrassDividedFourthShallowAtlasClosing
public import FLT.Mazur.WeierstrassDividedFourthShallowPreceding
public import FLT.Mazur.WeierstrassDividedFourthShallowAtlasSystem

/-!
# Simultaneous fifth factors on the entire depth-two atlas

Every retained label receives one whole-node factor, shared by both incident
edges. The initial open and terminal retain their complete fourth sources.
-/

@[expose] public noncomputable section
open AlgebraicGeometry CategoryTheory
namespace FLT.Mazur.WeierstrassDividedDepth
open PolygonArithmeticStages PolygonSmoothing WeierstrassModificationX
set_option backward.isDefEq.respectTransparency false
attribute [local irreducible] finiteGlobalModel finiteGlobalContraction
  arithmeticFourthShallowAtlasCorrection arithmeticFourthShallowAtlasChart
  arithmeticFifthShallowIso arithmeticFifthShallowNeighborIso
  arithmeticFifthShallowLastOrientedIso arithmeticFifthShallowPrecedingIso
  arithmeticFifthShallowTerminalIso
variable {R : Type} [CommRing R] [IsDomain R] [IsBezout R]
  {W : WeierstrassCurve R} {π : R} (hπ : π ≠ 0) {n : ℕ}
  (data : (i : Fin (n + 1)) → Data W π (1 + i.val))
  (H : ArithmeticAtlasCoefficients data) (m : ℕ) (hj : 3 ≤ n)
  (u : Rˣ) (hu : (data ⟨3, Nat.lt_succ_of_le hj⟩).b6 = π * ↑u)
local notation "Q" => Quotient R π m
local notation "τ" => arithmeticInitialMobiusSmoothing W H.a1_unit (π ^ 1) π m
local notation "B" => arithmeticFourthShallowAtlasObject hπ data H m 2 hj u hu
local notation "κ" => arithmeticFourthShallowAtlasChart hπ data H m 2 hj u hu
local notation "I" => arithmeticFourthShallowAtlasIso hπ data H m 2 hj u hu

/-- The fifth objects at each actual depth-two label, including the original infinity. -/
def arithmeticFifthShallowAtlasObject : ArithmeticChartLabel 3 → Scheme
  | .initial b => arithmeticFifthShallowObject hπ data H m 2 hj u hu b
  | .retained a b => match a.val with
    | 0 => PolygonSmoothing.chart Q
        (arithmeticFifthShallowNeighborSmoothing hπ data H 2 hj u hu m b)
    | 1 => PolygonSmoothing.chart Q
        (arithmeticFifthShallowPrecedingSmoothing hπ data H 2 hj u hu m b)
    | _ => PolygonSmoothing.chart Q τ
  | .terminal => PolygonSmoothing.chart Q
      (arithmeticFifthShallowTerminalSmoothing hπ data H 2 hj u hu m)
  | .infinity => B .infinity

local notation "A" => arithmeticFifthShallowAtlasObject hπ data H m hj u hu

/-- All fifth factors are installed together from the same fourth atlas. -/
def arithmeticFifthShallowAtlasCorrection (i : ArithmeticChartLabel 3) : B i ≅ A i :=
  match i with
  | .initial b =>
    (arithmeticFourthShallowIdentification hπ data H m 2 hj u hu rfl b).symm ≪≫
      arithmeticFifthShallowIso hπ data H m 2 hj u hu b
  | .retained ⟨0, _⟩ b =>
    (arithmeticFourthShallowNeighborIdentification hπ data H m 2 hj u hu rfl b).symm ≪≫
      arithmeticFifthShallowNeighborIso hπ data H m 2 hj u hu b
  | .retained ⟨1, _⟩ b =>
    (arithmeticFourthShallowPrecedingIdentification
      hπ data H m 2 hj u hu 1 rfl (by omega) b).symm ≪≫
      arithmeticFifthShallowPrecedingIso hπ data H m 2 hj u hu b
  | .retained ⟨2, _⟩ b =>
    (arithmeticFourthShallowLastIdentification hπ data H m 2 hj u hu b).symm ≪≫
      arithmeticFifthShallowLastOrientedIso hπ data H m 2 hj u hu b
  | .retained ⟨k + 3, hk⟩ _ => False.elim (by omega)
  | .terminal => arithmeticFifthShallowTerminalIso hπ data H m 2 hj u hu
  | .infinity => Iso.refl _

attribute [local irreducible] arithmeticFifthShallowAtlasCorrection
local notation "E" => arithmeticFifthShallowAtlasCorrection hπ data H m hj u hu

/-- The full fifth chart inclusion in the unchanged global target. -/
def arithmeticFifthShallowAtlasChart (i : ArithmeticChartLabel 3) :
    A i ⟶ simultaneousTwistedArithmeticStage hπ data H m 2 hj u hu :=
  (E i).inv ≫ κ i

instance arithmeticFifthShallowAtlasChart_isOpenImmersion (i : ArithmeticChartLabel 3) :
    IsOpenImmersion (arithmeticFifthShallowAtlasChart hπ data H m hj u hu i) := by
  unfold arithmeticFifthShallowAtlasChart
  infer_instance

/-- The comparison from each original chart includes all five complete correction rounds. -/
def arithmeticFifthShallowAtlasIso (i : ArithmeticChartLabel 3) :
    arithmeticLabeledAtlasObject hπ data H m 3 hj i ≅ A i := I i ≪≫ E i

local notation "ι" => arithmeticFifthShallowAtlasChart hπ data H m hj u hu

/-- The installed correction recovers the exact fourth inclusion at every label. -/
@[reassoc] theorem arithmeticFifthShallowAtlasCorrection_chart (i : ArithmeticChartLabel 3) :
    (E i).hom ≫ ι i = κ i := by
  rw [arithmeticFifthShallowAtlasChart, Iso.hom_inv_id_assoc]

/-- The original global inclusion is recovered by the composed full chart comparison. -/
@[reassoc] theorem arithmeticFifthShallowAtlasIso_chart (i : ArithmeticChartLabel 3) :
    arithmeticLabeledAtlasMap hπ data H m 3 hj i ≫
        (simultaneousTwistedArithmeticIso hπ data H m 2 hj u hu).hom =
      (arithmeticFifthShallowAtlasIso hπ data H m hj u hu i).hom ≫ ι i := by
  rw [arithmeticFifthShallowAtlasIso, Iso.trans_hom, Category.assoc,
    arithmeticFifthShallowAtlasCorrection_chart]
  exact arithmeticFourthShallowAtlasIso_chart hπ data H m 2 hj u hu i

attribute [local irreducible] arithmeticFifthShallowAtlasChart

/-- The simultaneous fifth factors transport the entire original cover. -/
def arithmeticFifthShallowOpenCover :
    (simultaneousTwistedArithmeticStage hπ data H m 2 hj u hu).OpenCover :=
  (arithmeticFourthShallowOpenCover hπ data H m 2 hj u hu).copy
    (ArithmeticChartLabel 3) A ι (Equiv.refl _) (fun i ↦ (E i).symm)
      (fun _ ↦ by rw [arithmeticFifthShallowAtlasChart]; rfl)

/-- Every point of the full global target remains covered by a fifth chart. -/
theorem arithmeticFifthShallowAtlas_cover
    (z : simultaneousTwistedArithmeticStage hπ data H m 2 hj u hu) :
    ∃ i x, ι i x = z := (arithmeticFifthShallowOpenCover hπ data H m hj u hu).exists_eq z

end FLT.Mazur.WeierstrassDividedDepth
