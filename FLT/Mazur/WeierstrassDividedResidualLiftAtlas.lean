/-
Copyright (c) 2026 krandder. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: krandder
-/
module

public import FLT.Mazur.WeierstrassDividedResidualLiftGeometry

/-!
# A complete arithmetic atlas after the lifted first residual corrections

Every original label remains in a full open cover at every arithmetic order.
The common terminal smoothing includes both drifts. This construction does
not assert that the new higher-order overlap residuals vanish.
-/

@[expose] public noncomputable section
open AlgebraicGeometry CategoryTheory
namespace FLT.Mazur.WeierstrassDividedDepth
open PolygonArithmeticStages PolygonSmoothing WeierstrassModificationX
set_option backward.isDefEq.respectTransparency false
attribute [local irreducible] finiteGlobalModel finiteGlobalContraction
variable {R : Type} [CommRing R] [IsDomain R] [IsBezout R]
  {W : WeierstrassCurve R} {π : R} (hπ : π ≠ 0) {n : ℕ}
  (data : (i : Fin (n + 1)) → Data W π (1 + i.val))
  (H : ArithmeticAtlasCoefficients data) (m j : ℕ) (hj : j + 1 ≤ n)
  (u : Rˣ) (hu : (data ⟨j + 1, Nat.lt_succ_of_le hj⟩).b6 = π * ↑u)
local notation "B" => changedArithmeticAtlasObject hπ data H m j hj u hu
local notation "κ" => changedArithmeticAtlasChart hπ data H m j hj u hu
local notation "I" => changedArithmeticAtlasIso hπ data H m j hj u hu
local notation "G" => simultaneousTwistedArithmeticIso hπ data H m j hj u hu
local notation "C" => arithmeticResidualLiftOrientedIso hπ data H m j hj u hu
local notation "F" => arithmeticResidualLiftTerminalIso hπ data H m j hj u hu

/-- The terminal label uses the full changed source, and every other label is retained. -/
def arithmeticResidualLiftAtlasObject : ArithmeticChartLabel (j + 1) → Scheme
  | .terminal => PolygonSmoothing.chart (Quotient R π m)
      (arithmeticResidualLiftTerminalSmoothing hπ data H m j hj u hu)
  | i => B i

local notation "A" => arithmeticResidualLiftAtlasObject hπ data H m j hj u hu

/-- The constructed full-chart correction, supported at the two closing pairs. -/
def arithmeticResidualLiftAtlasCorrection (i : ArithmeticChartLabel (j + 1)) : B i ≅ A i :=
  match i with
  | .terminal => F
  | .retained a b => if a.val = j then C b else Iso.refl _
  | .initial _ => Iso.refl _
  | .infinity => Iso.refl _

local notation "E" => arithmeticResidualLiftAtlasCorrection hπ data H m j hj u hu

/-- The actual corrected chart inclusions in the one complete target. -/
def arithmeticResidualLiftAtlasChart (i : ArithmeticChartLabel (j + 1)) :
    A i ⟶ simultaneousTwistedArithmeticStage hπ data H m j hj u hu :=
  (E i).inv ≫ κ i

instance arithmeticResidualLiftAtlasChart_isOpenImmersion
    (i : ArithmeticChartLabel (j + 1)) :
    IsOpenImmersion (arithmeticResidualLiftAtlasChart hπ data H m j hj u hu i) := by
  unfold arithmeticResidualLiftAtlasChart
  infer_instance

/-- Every original chart has a constructed comparison to its corrected full chart. -/
def arithmeticResidualLiftAtlasIso (i : ArithmeticChartLabel (j + 1)) :
    arithmeticLabeledAtlasObject hπ data H m (j + 1) hj i ≅ A i :=
  I i ≪≫ E i

local notation "c" => arithmeticLabeledAtlasMap hπ data H m (j + 1) hj
local notation "ι" => arithmeticResidualLiftAtlasChart hπ data H m j hj u hu
local notation "J" => arithmeticResidualLiftAtlasIso hπ data H m j hj u hu

/-- The full original chart inclusion is recovered after the two explicit corrections. -/
@[reassoc] theorem arithmeticResidualLiftAtlasIso_chart (i : ArithmeticChartLabel (j + 1)) :
    c i ≫ (G).hom = (J i).hom ≫ ι i := by
  rw [arithmeticResidualLiftAtlasIso, Iso.trans_hom, arithmeticResidualLiftAtlasChart,
    Category.assoc, Iso.hom_inv_id_assoc]
  exact changedArithmeticAtlasIso_chart hπ data H m j hj u hu i

/-- All corrected full charts still cover the entire global target. -/
theorem arithmeticResidualLiftAtlas_cover
    (z : simultaneousTwistedArithmeticStage hπ data H m j hj u hu) :
    ∃ i x, ι i x = z := by
  obtain ⟨i, x, rfl⟩ := changedArithmeticAtlas_cover hπ data H m j hj u hu z
  refine ⟨i, (E i).hom x, ?_⟩
  exact congrArg (fun f ↦ f x) (by
    rw [arithmeticResidualLiftAtlasChart, Iso.hom_inv_id_assoc] :
      (E i).hom ≫ ι i = κ i)

/-- A full labeled open cover, with one shared corrected terminal node. -/
def arithmeticResidualLiftOpenCover :
    (simultaneousTwistedArithmeticStage hπ data H m j hj u hu).OpenCover where
  I₀ := ArithmeticChartLabel (j + 1)
  X := A
  f := ι
  mem₀ := by
    rw [Scheme.presieve₀_mem_precoverage_iff]
    exact ⟨arithmeticResidualLiftAtlas_cover hπ data H m j hj u hu,
      fun i ↦ arithmeticResidualLiftAtlasChart_isOpenImmersion hπ data H m j hj u hu i⟩

end FLT.Mazur.WeierstrassDividedDepth
