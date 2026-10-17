/-
Copyright (c) 2026 krandder. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: krandder
-/
module

public import FLT.Mazur.WeierstrassDividedResidualLiftAtlas
public import FLT.Mazur.WeierstrassDividedSecondJointGeometry

/-!
# One full atlas with simultaneous second corrections

The last retained pair uses the shared two-branch correction. Its predecessor
pair keeps its new smoothing, and the common terminal uses the second inverse.
All labels, including the initial charts and infinity, remain in the cover.
-/

@[expose] public noncomputable section
open AlgebraicGeometry CategoryTheory
namespace FLT.Mazur.WeierstrassDividedDepth
open PolygonArithmeticStages PolygonSmoothing WeierstrassModificationX
set_option backward.isDefEq.respectTransparency false
attribute [local irreducible] finiteGlobalModel finiteGlobalContraction
  arithmeticSecondJointRetainedIso arithmeticSecondJointOrientedIso
  arithmeticSecondPrecedingIso arithmeticSecondPrecedingOrientedIso
  arithmeticSecondResidualLiftTerminalIso
variable {R : Type} [CommRing R] [IsDomain R] [IsBezout R]
  {W : WeierstrassCurve R} {π : R} (hπ : π ≠ 0) {n : ℕ}
  (data : (i : Fin (n + 1)) → Data W π (1 + i.val))
  (H : ArithmeticAtlasCoefficients data) (m j : ℕ) (hj : j + 1 ≤ n)
  (u : Rˣ) (hu : (data ⟨j + 1, Nat.lt_succ_of_le hj⟩).b6 = π * ↑u)
local notation "B" => arithmeticResidualLiftAtlasObject hπ data H m j hj u hu
local notation "κ" => arithmeticResidualLiftAtlasChart hπ data H m j hj u hu
local notation "I" => arithmeticResidualLiftAtlasIso hπ data H m j hj u hu
local notation "G" => simultaneousTwistedArithmeticIso hπ data H m j hj u hu
local notation "C" => arithmeticSecondJointOrientedIso hπ data H m j hj u hu
local notation "F" => arithmeticSecondResidualLiftTerminalIso hπ data H m j hj u hu

/-- Terminal and predecessor labels retain their exact changed smoothing parameters. -/
def arithmeticSecondJointAtlasObject : ArithmeticChartLabel (j + 1) → Scheme
  | .terminal => PolygonSmoothing.chart (Quotient R π m)
      (arithmeticSecondResidualLiftSmoothing hπ data H j hj u hu m)
  | .retained a b => if a.val + 1 = j then
      PolygonSmoothing.chart (Quotient R π m)
        (arithmeticSecondPrecedingSmoothing hπ data H m j hj u hu b)
      else B (.retained a b)
  | .initial b => B (.initial b)
  | .infinity => B .infinity

local notation "A" => arithmeticSecondJointAtlasObject hπ data H m j hj u hu

/-- Install the simultaneous corrections at the last and penultimate retained pairs. -/
def arithmeticSecondJointAtlasCorrection (i : ArithmeticChartLabel (j + 1)) : B i ≅ A i :=
  match i with
  | .terminal => F
  | .retained a b => by
      dsimp only [arithmeticSecondJointAtlasObject]
      split_ifs with hp
      · exact arithmeticSecondPrecedingOrientedIso hπ data H m j hj u hu b
      · exact if a.val = j then C b else Iso.refl _
  | .initial _ => Iso.refl _
  | .infinity => Iso.refl _

attribute [local irreducible] arithmeticSecondJointAtlasCorrection

local notation "E" => arithmeticSecondJointAtlasCorrection hπ data H m j hj u hu

/-- The actual corrected chart inclusions in the one complete target. -/
def arithmeticSecondJointAtlasChart (i : ArithmeticChartLabel (j + 1)) :
    A i ⟶ simultaneousTwistedArithmeticStage hπ data H m j hj u hu :=
  (E i).inv ≫ κ i

instance arithmeticSecondJointAtlasChart_isOpenImmersion
    (i : ArithmeticChartLabel (j + 1)) :
    IsOpenImmersion (arithmeticSecondJointAtlasChart hπ data H m j hj u hu i) := by
  unfold arithmeticSecondJointAtlasChart
  infer_instance

/-- Every original chart has a constructed comparison to its corrected full chart. -/
def arithmeticSecondJointAtlasIso (i : ArithmeticChartLabel (j + 1)) :
    arithmeticLabeledAtlasObject hπ data H m (j + 1) hj i ≅ A i :=
  I i ≪≫ E i

local notation "c" => arithmeticLabeledAtlasMap hπ data H m (j + 1) hj
local notation "ι" => arithmeticSecondJointAtlasChart hπ data H m j hj u hu
local notation "J" => arithmeticSecondJointAtlasIso hπ data H m j hj u hu

/-- The full original chart inclusion is recovered after the two explicit corrections. -/
@[reassoc] theorem arithmeticSecondJointAtlasIso_chart (i : ArithmeticChartLabel (j + 1)) :
    c i ≫ (G).hom = (J i).hom ≫ ι i := by
  rw [arithmeticSecondJointAtlasIso, Iso.trans_hom, arithmeticSecondJointAtlasChart,
    Category.assoc, Iso.hom_inv_id_assoc]
  exact arithmeticResidualLiftAtlasIso_chart hπ data H m j hj u hu i

attribute [local irreducible] arithmeticSecondJointAtlasChart arithmeticResidualLiftAtlasChart

/-- The original complete open cover transported through the installed node corrections. -/
def arithmeticSecondJointOpenCover :
    (simultaneousTwistedArithmeticStage hπ data H m j hj u hu).OpenCover :=
  (arithmeticResidualLiftOpenCover hπ data H m j hj u hu).copy
    (ArithmeticChartLabel (j + 1)) A ι (Equiv.refl _) (fun i ↦ (E i).symm)
      (fun _ ↦ by rw [arithmeticSecondJointAtlasChart]; rfl)

/-- All corrected full charts still cover the entire global target. -/
theorem arithmeticSecondJointAtlas_cover
    (z : simultaneousTwistedArithmeticStage hπ data H m j hj u hu) :
    ∃ i x, ι i x = z :=
  (arithmeticSecondJointOpenCover hπ data H m j hj u hu).exists_eq z

end FLT.Mazur.WeierstrassDividedDepth
