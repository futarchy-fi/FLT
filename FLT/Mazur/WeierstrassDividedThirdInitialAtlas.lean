/-
Copyright (c) 2026 krandder. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: krandder
-/
module

public import FLT.Mazur.WeierstrassDividedThirdInitialGeometry

/-!
# Install the corrected original initial opens at depth one

At depth one the two original initial charts receive their full positive
node factors. All retained labels and the terminal keep the third atlas.
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
local notation "B" => arithmeticThirdAtlasObject hπ data H m j hj u hu
local notation "κ" => arithmeticThirdAtlasChart hπ data H m j hj u hu
local notation "C" => arithmeticThirdInitialIso hπ data H m j hj u hu

/-- Only the depth-one initial labels receive the constructed corrected initial open. -/
def arithmeticThirdInitialAtlasObject : ArithmeticChartLabel (j + 1) → Scheme
  | .initial b => if j = 1 then arithmeticThirdInitialObject hπ data H m j hj u hu b
      else B (.initial b)
  | i => B i

local notation "A" => arithmeticThirdInitialAtlasObject hπ data H m j hj u hu

/-- Install the full original initial correction only at depth one. -/
def arithmeticThirdInitialAtlasCorrection (i : ArithmeticChartLabel (j + 1)) : B i ≅ A i :=
  match i with
  | .initial b => if h : j = 1 then
      C b ≪≫ eqToIso (by simp only [arithmeticThirdInitialAtlasObject, h, ↓reduceIte])
      else eqToIso (by simp only [arithmeticThirdInitialAtlasObject, h, ↓reduceIte])
  | .retained _ _ => Iso.refl _
  | .terminal => Iso.refl _
  | .infinity => Iso.refl _

local notation "E" => arithmeticThirdInitialAtlasCorrection hπ data H m j hj u hu

/-- The new full initial opens map into the actual complete arithmetic target. -/
def arithmeticThirdInitialAtlasChart (i : ArithmeticChartLabel (j + 1)) :
    A i ⟶ simultaneousTwistedArithmeticStage hπ data H m j hj u hu :=
  (E i).inv ≫ κ i

local notation "ι" => arithmeticThirdInitialAtlasChart hπ data H m j hj u hu

instance arithmeticThirdInitialAtlasChart_isOpenImmersion (i : ArithmeticChartLabel (j + 1)) :
    IsOpenImmersion (ι i) := by
  unfold arithmeticThirdInitialAtlasChart
  infer_instance

/-- The initial correction recovers its actual full third-atlas inclusion. -/
@[reassoc] theorem arithmeticThirdInitialAtlasCorrection_chart
    (i : ArithmeticChartLabel (j + 1)) : (E i).hom ≫ ι i = κ i := by
  rw [arithmeticThirdInitialAtlasChart, Iso.hom_inv_id_assoc]

/-- Every retained chart keeps its full third geometry and its global inclusion. -/
theorem arithmeticThirdInitialAtlasChart_retained (a : Fin (j + 1)) (b : Bool) :
    ι (.retained a b) = κ (.retained a b) := by
  change 𝟙 _ ≫ κ (.retained a b) = _
  exact Category.id_comp _

/-- The terminal's complete third correction is unchanged. -/
theorem arithmeticThirdInitialAtlasChart_terminal : ι .terminal = κ .terminal := by
  change 𝟙 _ ≫ κ .terminal = _
  exact Category.id_comp _

/-- The complete original chart comparison includes the newly corrected initial open. -/
def arithmeticThirdInitialAtlasIso (i : ArithmeticChartLabel (j + 1)) :
    arithmeticLabeledAtlasObject hπ data H m (j + 1) hj i ≅ A i :=
  arithmeticThirdAtlasIso hπ data H m j hj u hu i ≪≫ E i

/-- This comparison recovers every original global chart map. -/
@[reassoc] theorem arithmeticThirdInitialAtlasIso_chart (i : ArithmeticChartLabel (j + 1)) :
    arithmeticLabeledAtlasMap hπ data H m (j + 1) hj i ≫
        (simultaneousTwistedArithmeticIso hπ data H m j hj u hu).hom =
      (arithmeticThirdInitialAtlasIso hπ data H m j hj u hu i).hom ≫ ι i := by
  rw [arithmeticThirdInitialAtlasIso, Iso.trans_hom, Category.assoc,
    arithmeticThirdInitialAtlasCorrection_chart]
  exact arithmeticThirdAtlasIso_chart hπ data H m j hj u hu i

attribute [local irreducible] arithmeticThirdInitialAtlasChart arithmeticThirdAtlasChart

/-- Transport the entire cover, including infinity, through the actual initial factors. -/
def arithmeticThirdInitialOpenCover :
    (simultaneousTwistedArithmeticStage hπ data H m j hj u hu).OpenCover :=
  (arithmeticThirdOpenCover hπ data H m j hj u hu).copy
    (ArithmeticChartLabel (j + 1)) A ι (Equiv.refl _) (fun i ↦ (E i).symm)
      (fun _ ↦ by rw [arithmeticThirdInitialAtlasChart]; rfl)

/-- The corrected initial charts still belong to a cover of the entire original target. -/
theorem arithmeticThirdInitialAtlas_cover
    (z : simultaneousTwistedArithmeticStage hπ data H m j hj u hu) :
    ∃ i x, ι i x = z := (arithmeticThirdInitialOpenCover hπ data H m j hj u hu).exists_eq z

end FLT.Mazur.WeierstrassDividedDepth
