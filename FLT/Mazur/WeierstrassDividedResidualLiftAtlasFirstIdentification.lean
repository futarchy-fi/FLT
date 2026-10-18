/-
Copyright (c) 2026 krandder. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: krandder
-/
module

public import FLT.Mazur.WeierstrassDividedResidualLiftFirst
public import FLT.Mazur.WeierstrassDividedResidualLiftAtlas
public import FLT.Mazur.WeierstrassDividedFirstResidualAtlas

/-!
# Full first-order identification of the lifted residual atlas

The whole common terminal is identified through its proved smoothing equality.
All retained orientations and both original initial labels are preserved.
The primitive b6 hypothesis and the unchanged depth parameter remain explicit.
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
  (H : ArithmeticAtlasCoefficients data) (j : ℕ) (hj : j + 1 ≤ n)
  (u : Rˣ) (hu : (data ⟨j + 1, Nat.lt_succ_of_le hj⟩).b6 = π * ↑u)
local notation "A" => arithmeticResidualLiftAtlasObject hπ data H 1 j hj u hu
local notation "B" => changedArithmeticAtlasObject hπ data H 1 j hj u hu
local notation "E" => arithmeticResidualLiftAtlasCorrection hπ data H 1 j hj u hu
local notation "F" => arithmeticFirstResidualAtlasCorrection hπ data H j hj u hu
local notation "s" => arithmeticResidualLiftTerminalSmoothing hπ data H 1 j hj u hu
local notation "σ" => arithmeticTerminalChangedSmoothing data H 1 j hj u hu

/-- Every lifted full chart has its proved first-order identification. -/
def arithmeticResidualLiftAtlasFirstIdentification
    (i : ArithmeticChartLabel (j + 1)) : A i ≅ B i :=
  match i with
  | .terminal => nodeParameterIso s σ
      (arithmeticResidualLiftTerminalSmoothing_first hπ data H j hj u hu)
  | .retained _ _ => Iso.refl _
  | .initial _ => Iso.refl _
  | .infinity => Iso.refl _

local notation "J" => arithmeticResidualLiftAtlasFirstIdentification hπ data H j hj u hu

omit [IsBezout R] in
/-- The entire first-order correction agrees at every label, including the common terminal. -/
theorem arithmeticResidualLiftAtlasCorrection_first (i : ArithmeticChartLabel (j + 1)) :
    E i ≪≫ J i = F i := by
  cases i with
  | terminal => exact arithmeticResidualLiftTerminalIso_first hπ data H j hj u hu
  | retained a b =>
    by_cases h : a.val = j
    · simpa only [arithmeticResidualLiftAtlasCorrection,
        arithmeticResidualLiftAtlasFirstIdentification, arithmeticFirstResidualAtlasCorrection,
        h, ↓reduceIte, Iso.trans_refl] using
          arithmeticResidualLiftOrientedIso_first hπ data H j hj u hu b
    · simp only [arithmeticResidualLiftAtlasCorrection,
        arithmeticResidualLiftAtlasFirstIdentification, arithmeticFirstResidualAtlasCorrection,
        h, ↓reduceIte, Iso.trans_refl]
  | initial b => exact Iso.trans_refl _
  | infinity => exact Iso.trans_refl _

/-- The first-order identification commutes with the full inclusion in the original target. -/
@[reassoc] theorem arithmeticResidualLiftAtlasFirstIdentification_chart
    (i : ArithmeticChartLabel (j + 1)) :
    (J i).hom ≫ arithmeticFirstResidualAtlasChart hπ data H j hj u hu i =
      arithmeticResidualLiftAtlasChart hπ data H 1 j hj u hu i := by
  apply (cancel_epi (E i).hom).mp
  rw [← Category.assoc]
  have h := congrArg Iso.hom (arithmeticResidualLiftAtlasCorrection_first hπ data H j hj u hu i)
  rw [Iso.trans_hom] at h
  rw [h, arithmeticFirstResidualAtlasChart, arithmeticResidualLiftAtlasChart,
    Iso.hom_inv_id_assoc, Iso.hom_inv_id_assoc]

omit [IsBezout R] in
/-- The complete original-chart comparison recovers its former first-order isomorphism. -/
theorem arithmeticResidualLiftAtlasIso_first (i : ArithmeticChartLabel (j + 1)) :
    arithmeticResidualLiftAtlasIso hπ data H 1 j hj u hu i ≪≫ J i =
      arithmeticFirstResidualAtlasIso hπ data H j hj u hu i := by
  rw [arithmeticResidualLiftAtlasIso, arithmeticFirstResidualAtlasIso, Iso.trans_assoc,
    arithmeticResidualLiftAtlasCorrection_first]

end FLT.Mazur.WeierstrassDividedDepth
