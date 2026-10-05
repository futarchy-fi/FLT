/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.SectionGradedChartEvaluation
public import FLT.Mazur.SectionGradedProjConstruction

/-!
# Scheme maps from the intrinsic generator-chart comparison

The ring comparison defines a map from every generator subopen into Proj.
It restricts naturally and agrees with the canonical map in any line
coordinates, hence with the globally glued canonical morphism.
-/

@[expose] public noncomputable section
open CategoryTheory AlgebraicGeometry
open Scheme.Modules
namespace FLT.Mazur.SectionGradedChartMorphism
open FCurve ModuleLineBundleTensorPullback SectionGradedMultiplication SectionGradedSum
open SectionGradedChartComparison SectionGradedProjConstruction
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
variable {X : Scheme} (L : X.Modules) [hL : Fact (LocallyFreeRankOne L)]
  (d : ℕ) (s : Piece L ⊤ d) (hd : 0 < d)

/-- The intrinsic chart comparison defines an actual morphism into the original Proj. -/
def toProjOn (U : X.Opens) (hU : U ≤ sectionGeneratorOpen (tensorPower L d) s) :
    U.toScheme ⟶ Proj (grade L ⊤) :=
  U.toSpecΓ ≫ Spec.map (CommRingCat.ofHom (toFunctions L d s U hU)) ≫
    Proj.awayι (grade L ⊤) (of L ⊤ d s) ⟨s, rfl⟩ hd

/-- The intrinsic chart morphism commutes with restriction to a smaller generator subopen. -/
@[reassoc]
lemma toProjOn_restrict {U V : X.Opens} (hVU : V ≤ U)
    (hU : U ≤ sectionGeneratorOpen (tensorPower L d) s) :
    X.homOfLE hVU ≫ toProjOn L d s hd U hU =
      toProjOn L d s hd V (hVU.trans hU) := by
  have hφ : CommRingCat.ofHom (toFunctions L d s U hU) ≫
      X.presheaf.map (homOfLE hVU).op =
      CommRingCat.ofHom (toFunctions L d s V (hVU.trans hU)) :=
    CommRingCat.hom_ext (SectionGradedChartRatios.toFunctions_restrict L d s hVU hU)
  unfold toProjOn
  rw [← Category.assoc, ← Scheme.Opens.toSpecΓ_SpecMap_presheaf_map,
    Category.assoc, ← Spec.map_comp_assoc, hφ]

/-- On a trivializing generator subopen the intrinsic map is the coordinate Proj chart. -/
lemma toProjOn_eq_chart (U : X.Opens)
    (hU : U ≤ sectionGeneratorOpen (tensorPower L d) s)
    (e : (pullback U.ι).obj L ≅ structureModule U.toScheme) :
    toProjOn L d s hd U hU = SectionGradedProjChart.generatorChart L U e s hd hU := by
  let hs := SectionGradedProjChart.ringHom_of_isUnit L U e s hU
  have he := SectionGradedChartEvaluation.toFunctions_evaluation L U.ι e d s
    (U.ι_image_top.le.trans hU) hs
  rw [Scheme.Opens.ι_appIso] at he
  have hr := SectionGradedChartRatios.toFunctions_restrict L d s U.ι_image_top.le hU
  have hφ : U.topIso.inv.hom.comp (toFunctions L d s U hU) =
      SectionGradedProjChart.evaluation U.ι L e (of L ⊤ d s) hs := by
    exact hr.trans he
  have hφ' : CommRingCat.ofHom (toFunctions L d s U hU) ≫ U.topIso.inv =
      CommRingCat.ofHom (SectionGradedProjChart.evaluation U.ι L e (of L ⊤ d s) hs) :=
    CommRingCat.hom_ext hφ
  unfold toProjOn Scheme.Opens.toSpecΓ SectionGradedProjChart.generatorChart
    SectionGradedProjChart.toProj GradedProjUnitChart.toProj GradedProjUnitChart.toAffine
  rw [Category.assoc, ← Spec.map_comp_assoc, hφ', Category.assoc]
  rfl

/-- The intrinsic generator-chart morphism is the restriction of the actual canonical map. -/
lemma toProjOn_eq (h : PositivePowerGenerated L) (U : X.Opens)
    (hU : U ≤ sectionGeneratorOpen (tensorPower L d) s) :
    toProjOn L d s hd U hU = U.ι ≫ toProj L h := by
  choose W hW e using fun x : U ↦ hL.out (x : X)
  let V (x : U) : X.Opens := U ⊓ W x
  let j (x : U) : (V x).toScheme ⟶ U.toScheme := X.homOfLE inf_le_left
  let C : U.toScheme.OpenCover := ⟨⟨_, fun x : U ↦ (V x).toScheme, j⟩,
    ⟨by
      simpa using show ∀ x : U.toScheme, ∃ y z, j y z = x from fun x ↦
        ⟨x, ⟨x.1, x.2, hW x⟩, Subtype.ext (Scheme.homOfLE_apply _ _)⟩,
      by simpa [j] using (fun x : U ↦ (inferInstance :
        IsOpenImmersion (X.homOfLE (U := V x) (V := U) inf_le_left)))⟩⟩
  apply C.hom_ext
  intro x
  let eV : (pullback (V x).ι).obj L ≅ structureModule (V x).toScheme :=
    ((restrictFunctorIsoPullback (V x).ι).app L).symm ≪≫
      ModuleSheafTensor.restrictTrivialization (show V x ≤ W x from inf_le_right) (e x).some
  change j x ≫ toProjOn L d s hd U hU = j x ≫ (U.ι ≫ toProj L h)
  rw [← Category.assoc, show j x ≫ U.ι = (V x).ι from Scheme.homOfLE_ι _ _]
  rw [toProj_generatorChart L h (V x) eV s hd (inf_le_left.trans hU)]
  exact (toProjOn_restrict L d s hd inf_le_left hU).trans
    (toProjOn_eq_chart L d s hd (V x) (inf_le_left.trans hU) eV)

end FLT.Mazur.SectionGradedChartMorphism
