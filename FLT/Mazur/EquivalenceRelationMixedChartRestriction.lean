/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.EquivalenceRelationMixedChartProjections

/-!
# Independent restrictions of entire mixed chart relations

Shrinking either source chart restricts the full mixed relation, with both
projections and the exact closed boundary unchanged on the smaller domain.
-/

@[expose] public noncomputable section
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
namespace FLT.Mazur.EquivalenceRelationNormalizedFrames.MixedFrames
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
variable {D A B : Scheme.{0}} {p q : D ⟶ A} [IsSeparated p]
  {I J : Type} [Fintype I] [Fintype J] (o : I) (o' : J)
  (U U' : (source p q I o).Opens) (V V' : (source p q J o').Opens)
  (hU : U' ≤ U) (hV : V' ≤ V)
local notation "M" => mixedChartOpen o o' U V
local notation "M'" => mixedChartOpen o o' U' V'

include hU hV in
/-- Independent chart refinement retains the whole smaller mixed relation. -/
theorem mixedChartOpen_mono : M' ≤ M :=
  inf_le_inf ((fst p q I J o o').preimage_mono hU) ((snd p q I J o o').preimage_mono hV)

/-- The actual inclusion of the smaller full mixed relation. -/
def mixedChartRestriction : (M').toScheme ⟶ (M).toScheme :=
  (relation p q I J o o').homOfLE (mixedChartOpen_mono o o' U U' V V' hU hV)

/-- The first projection commutes with independent chart refinement. -/
@[reassoc] theorem mixedChartRestriction_first :
    mixedChartRestriction o o' U U' V V' hU hV ≫ mixedChartFirst o o' U V =
      mixedChartFirst o o' U' V' ≫ (source p q I o).homOfLE hU := by
  apply (cancel_mono U.ι).mp
  simp only [Category.assoc, mixedChartFirst, Scheme.Hom.resLE_comp_ι,
    Scheme.homOfLE_ι, mixedChartRestriction, Scheme.homOfLE_ι_assoc]

/-- The second projection commutes with independent chart refinement. -/
@[reassoc] theorem mixedChartRestriction_second :
    mixedChartRestriction o o' U U' V V' hU hV ≫ mixedChartSecond o o' U V =
      mixedChartSecond o o' U' V' ≫ (source p q J o').homOfLE hV := by
  apply (cancel_mono V.ι).mp
  simp only [Category.assoc, mixedChartSecond, Scheme.Hom.resLE_comp_ι,
    Scheme.homOfLE_ι, mixedChartRestriction, Scheme.homOfLE_ι_assoc]

variable (i : B ⟶ A)
local notation "j" => jointBoundaryTargetInclusion (p := p) (q := q) o o' i

/-- The full closed boundary of the smaller relation maps to the full original boundary. -/
def mixedChartBoundaryRestriction :
    (mixedChartBoundaryOpen o o' U' V' i).toScheme ⟶
      (mixedChartBoundaryOpen o o' U V i).toScheme :=
  (jointBoundaryTarget (p := p) (q := q) o o' i).homOfLE
    ((j).preimage_mono (mixedChartOpen_mono o o' U U' V V' hU hV))

/-- Restriction commutes with the exact closed boundary, including its nonreduced structure. -/
@[reassoc] theorem mixedChartBoundaryRestriction_ambient :
    mixedChartBoundaryRestriction o o' U U' V V' hU hV i ≫
        mixedChartBoundaryInclusion o o' U V i =
      mixedChartBoundaryInclusion o o' U' V' i ≫
        mixedChartRestriction o o' U U' V V' hU hV := by
  exact (morphismRestrict_homOfLE j M' M
    (mixedChartOpen_mono o o' U U' V V' hU hV)).symm

end FLT.Mazur.EquivalenceRelationNormalizedFrames.MixedFrames
