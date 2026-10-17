/-
Copyright (c) 2026 krandder. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: krandder
-/
module

public import FLT.Mazur.WeierstrassDividedResidualLiftAtlas
public import FLT.Mazur.WeierstrassDividedTerminalChangedAtlasSystem
public import FLT.Mazur.PolygonArithmeticTwoBranchRebaseNaturality

/-!
# Quotient-compatible complete atlases after the lifted residual corrections

Transport the actual arithmetic restrictions through the constructed full
chart comparisons. The resulting sequence has all original labels and exact
quotient squares. Its terminal arrow is explicitly the coefficient restriction
on the inversely rebased smoothing.
-/

@[expose] public noncomputable section
open AlgebraicGeometry CategoryTheory
namespace FLT.Mazur.WeierstrassDividedDepth
open PolygonArithmeticStages PolygonSmoothing
set_option backward.isDefEq.respectTransparency false
attribute [local irreducible] finiteGlobalModel finiteGlobalContraction
variable {R : Type} [CommRing R] [IsDomain R] [IsBezout R]
  {W : WeierstrassCurve R} {π : R} (hπ : π ≠ 0) {n : ℕ}
  (data : (i : Fin (n + 1)) → Data W π (1 + i.val))
  (H : ArithmeticAtlasCoefficients data) (j : ℕ) (hj : j + 1 ≤ n)
  (u : Rˣ) (hu : (data ⟨j + 1, Nat.lt_succ_of_le hj⟩).b6 = π * ↑u)
local notation "A" => fun m ↦ arithmeticResidualLiftAtlasObject hπ data H m j hj u hu
local notation "E" => fun m ↦ arithmeticResidualLiftAtlasCorrection hπ data H m j hj u hu
local notation "ι" => fun m ↦ arithmeticResidualLiftAtlasChart hπ data H m j hj u hu
local notation "ρ" => changedArithmeticAtlasRestriction hπ data H j hj u hu
local notation "q" => simultaneousTwistedArithmeticRestriction hπ data H

/-- The original arithmetic quotient transported through the actual whole-chart corrections. -/
def arithmeticResidualLiftAtlasRestriction (m : ℕ) (i : ArithmeticChartLabel (j + 1)) :
    A m i ⟶ A (m + 1) i :=
  (E m i).inv ≫ ρ m i ≫ (E (m + 1) i).hom

local notation "S" => arithmeticResidualLiftAtlasRestriction hπ data H j hj u hu

omit [IsBezout R] in
/-- Each correction is an exact square for the original arithmetic quotient. -/
@[reassoc] theorem arithmeticResidualLiftAtlasCorrection_restriction
    (m : ℕ) (i : ArithmeticChartLabel (j + 1)) :
    (E m i).hom ≫ S m i = ρ m i ≫ (E (m + 1) i).hom := by
  rw [arithmeticResidualLiftAtlasRestriction, Iso.hom_inv_id_assoc]

/-- Every full lifted chart inclusion respects the actual global quotient arrow. -/
@[reassoc] theorem arithmeticResidualLiftAtlasChart_restriction
    (m : ℕ) (i : ArithmeticChartLabel (j + 1)) :
    S m i ≫ ι (m + 1) i = ι m i ≫ q m j hj u hu := by
  dsimp only
  rw [arithmeticResidualLiftAtlasRestriction, arithmeticResidualLiftAtlasChart,
    arithmeticResidualLiftAtlasChart, Category.assoc, Category.assoc,
    Iso.hom_inv_id_assoc, changedArithmeticAtlasChart_restriction, Category.assoc]

/-- One full corrected labeled chart at every arithmetic quotient order. -/
def arithmeticResidualLiftChartSystem (i : ArithmeticChartLabel (j + 1)) : ℕ ⥤ Scheme :=
  Functor.ofSequence (fun m ↦ S m i)

/-- The complete lifted cover maps naturally into the original complete arithmetic target. -/
def arithmeticResidualLiftChartSystemMap (i : ArithmeticChartLabel (j + 1)) :
    arithmeticResidualLiftChartSystem hπ data H j hj u hu i ⟶
      changedArithmeticTargetSystem hπ data H j hj u hu :=
  NatTrans.ofSequence (fun m ↦ ι m i) (by
    intro m
    simpa only [arithmeticResidualLiftChartSystem, changedArithmeticTargetSystem,
      Functor.ofSequence_obj, Functor.ofSequence_map_homOfLE_succ] using
        arithmeticResidualLiftAtlasChart_restriction hπ data H j hj u hu m i)

/-- The complete chart comparison is compatible with every nonconsecutive quotient too. -/
@[reassoc] theorem arithmeticResidualLiftChartSystemMap_naturality
    (i : ArithmeticChartLabel (j + 1)) {a b : ℕ} (hab : a ≤ b) :
    (arithmeticResidualLiftChartSystem hπ data H j hj u hu i).map (homOfLE hab) ≫ ι b i =
      ι a i ≫ (changedArithmeticTargetSystem hπ data H j hj u hu).map (homOfLE hab) :=
  (arithmeticResidualLiftChartSystemMap hπ data H j hj u hu i).naturality (homOfLE hab)

local notation "σ" => fun m ↦ arithmeticTerminalChangedSmoothing data H m j hj u hu
local notation "s" => fun m ↦ arithmeticResidualLiftTerminalSmoothing hπ data H m j hj u hu
local notation "F" => fun m ↦ arithmeticResidualLiftTerminalIso hπ data H m j hj u hu

omit [IsBezout R] in
/-- The transported terminal arrow is the explicit coefficient restriction on its new smoothing. -/
theorem arithmeticResidualLiftAtlasRestriction_terminal (m : ℕ) :
    S m .terminal = Spec.map (CommRingCat.ofHom
      (ringMap (restriction R π m).toRingHom (s (m + 1)) (s m)
        (twoBranchCorrectionRebasedSmoothing_restriction R π m _ _
          (arithmeticTerminalChangedSmoothing_restriction data H m j hj u hu hπ) _))) := by
  apply (cancel_mono (F (m + 1)).inv).mp
  change ((F m).inv ≫ arithmeticTerminalChangedRestriction hπ data H m j hj u hu ≫
    (F (m + 1)).hom) ≫ (F (m + 1)).inv = _
  rw [Category.assoc, Category.assoc, Iso.hom_inv_id, Category.comp_id]
  change Spec.map _ ≫ Spec.map _ = Spec.map _ ≫ Spec.map _
  rw [← Spec.map_comp, ← Spec.map_comp]
  exact congrArg Spec.map (CommRingCat.hom_ext
    (twoBranchCorrectionRebasedFactor_restriction R π m (σ (m + 1)) (σ m)
      (arithmeticTerminalChangedSmoothing_restriction data H m j hj u hu hπ) _).symm)

end FLT.Mazur.WeierstrassDividedDepth
