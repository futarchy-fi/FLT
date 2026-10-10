/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.DualAtlasIteratedFrames
public import FLT.Mazur.ProjectiveCoefficientFunctor

/-!
# Composition of the original geometric dual atlas chart maps

Consecutive original projective chart morphisms agree with the composite
base-change chart map after the genuine ambient sheaf comparison.
-/

@[expose] public noncomputable section
open CategoryTheory AlgebraicGeometry
open Scheme.Modules
universe u
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
namespace FLT.Mazur.DualAtlasIteratedCharts
open FCurve AffineFiniteFreeAtlas DualAtlasBaseChangeCharts
open ProjectiveSpace DualFreeSheafCoordinates
variable {X Y Z : Scheme.{u}} (f : X ⟶ Y) (g : Y ⟶ Z) (M : Z.Modules)

/-- Original geometric chart maps compose through the actual ambient comparison. -/
lemma chartMap_comp (c : Chart f g M) :
    DualAtlasBaseChangeCharts.chartMap f ((pullback g).obj M)
        c.source c.middle c.first_le ≫
        DualAtlasBaseChangeCharts.chartMap g M c.middle c.target c.second_le =
      (DualAtlasAmbient.chartIso ((pullbackComp f g).app M) c.source).hom ≫
        DualAtlasBaseChangeCharts.chartMap (f ≫ g) M (c.composite f g M).source
          c.target (c.composite f g M).le_preimage := by
  erw [chartMap_eq f _ (c.first f g M), chartMap_eq g M (c.second f g M),
    chartMap_eq (f ≫ g) M (c.composite f g M)]
  change (_ ≫ _) ≫ _ ≫ _ =
    (projectiveIso (DualAtlasAmbient.change ((pullbackComp f g).app M) c.source)).hom ≫ _
  simp only [Category.assoc]
  rw [projectiveIso_pullback_assoc, ← Category.assoc, ← Iso.trans_hom,
    ← projectiveIso_trans]
  erw [← chartChange_comp f g M c]
  rw [projectiveIso_trans, Iso.trans_hom, Category.assoc,
    coefficientMap_appTop_comp]
  erw [baseMap_comp f g M c]
  rfl

end FLT.Mazur.DualAtlasIteratedCharts
