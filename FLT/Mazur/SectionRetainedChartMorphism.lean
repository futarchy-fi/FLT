/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.SectionRetainedProjConstruction
public import FLT.Mazur.SectionGradedChartEvaluation

/-!
# Intrinsic generator charts for the retained Proj map

The comparison with original chart functions gives a coordinate-free local
morphism. It agrees with the glued retained Proj morphism on every generator
subopen, including nonreduced schemes.
-/

@[expose] public noncomputable section

open CategoryTheory AlgebraicGeometry Scheme.Modules

namespace FLT.Mazur.SectionRetainedChartMorphism

open FCurve ModuleLineBundleTensorPullback SectionGradedSum
open SectionRetainedChartComparison SectionRetainedProjConstruction

set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true

variable {X : Scheme} (L : X.Modules) [hL : Fact (LocallyFreeRankOne L)]
  (q : ℕ) [GradedRing (RetainedSubringGrading.grade (grade L ⊤) q)]
  (d : ℕ) (s : Γ(tensorPower L (q * d), ⊤)) (hd : 0 < d)

/-- The original function comparison defines the intrinsic retained Proj chart. -/
def toProjOn (U : X.Opens) (hU : U ≤ sectionGeneratorOpen (tensorPower L (q * d)) s) :
    U.toScheme ⟶ Proj (RetainedSubringGrading.grade (grade L ⊤) q) :=
  U.toSpecΓ ≫ Spec.map (CommRingCat.ofHom (toFunctions L q d s U hU)) ≫
    Proj.awayι _ (insertion L q d s) (insertion_mem L q d s) hd

/-- The retained intrinsic chart restricts along the actual inclusion of generator subopens. -/
@[reassoc]
theorem toProjOn_restrict {U V : X.Opens} (hVU : V ≤ U)
    (hU : U ≤ sectionGeneratorOpen (tensorPower L (q * d)) s) :
    X.homOfLE hVU ≫ toProjOn L q d s hd U hU =
      toProjOn L q d s hd V (hVU.trans hU) := by
  have hφ : CommRingCat.ofHom (toFunctions L q d s U hU) ≫
      X.presheaf.map (homOfLE hVU).op =
      CommRingCat.ofHom (toFunctions L q d s V (hVU.trans hU)) :=
    CommRingCat.hom_ext (toFunctions_restrict L q d s hVU hU)
  unfold toProjOn
  rw [← Category.assoc, ← Scheme.Opens.toSpecΓ_SpecMap_presheaf_map,
    Category.assoc, ← Spec.map_comp_assoc, hφ]

/-- In line coordinates the intrinsic retained chart is the original retained evaluation. -/
theorem toProjOn_eq_chart (U : X.Opens)
    (hU : U ≤ sectionGeneratorOpen (tensorPower L (q * d)) s)
    (e : (pullback U.ι).obj L ≅ structureModule U.toScheme) :
    toProjOn L q d s hd U hU = SectionRetainedProjChart.toProj U.ι L e q
      (insertion L q d s) (SectionGradedProjChart.ringHom_of_isUnit L U e s hU)
      (insertion_mem L q d s) hd := by
  let hs := SectionGradedProjChart.ringHom_of_isUnit L U e s hU
  have he := SectionGradedChartEvaluation.toFunctions_evaluation L U.ι e (q * d) s
    (U.ι_image_top.le.trans hU) hs
  rw [Scheme.Opens.ι_appIso] at he
  have hr := SectionGradedChartRatios.toFunctions_restrict L (q * d) s U.ι_image_top.le hU
  have hfull : U.topIso.inv.hom.comp
      (SectionGradedChartComparison.toFunctions L (q * d) s U hU) =
      SectionGradedProjChart.evaluation U.ι L e (of L ⊤ (q * d) s) hs := hr.trans he
  have hφ : U.topIso.inv.hom.comp (toFunctions L q d s U hU) =
      GradedProjUnitChart.evaluation _ (SectionRetainedProjChart.ringHom U.ι L e q)
        (insertion L q d s) hs := by
    rw [toFunctions, ← RingHom.comp_assoc, hfull, SectionRetainedProjChart.evaluation_eq]
    rfl
  have hφ' : CommRingCat.ofHom (toFunctions L q d s U hU) ≫ U.topIso.inv =
      CommRingCat.ofHom (GradedProjUnitChart.evaluation _
        (SectionRetainedProjChart.ringHom U.ι L e q) (insertion L q d s) hs) :=
    CommRingCat.hom_ext hφ
  unfold toProjOn Scheme.Opens.toSpecΓ SectionRetainedProjChart.toProj
    GradedProjUnitChart.toProj GradedProjUnitChart.toAffine
  rw [Category.assoc, ← Spec.map_comp_assoc, hφ', Category.assoc]

/-- The intrinsic retained generator chart is the restriction of the constructed global map. -/
theorem toProjOn_eq (h : PositivePowerGenerated L q) (U : X.Opens)
    (hU : U ≤ sectionGeneratorOpen (tensorPower L (q * d)) s) :
    toProjOn L q d s hd U hU = U.ι ≫ toProj L q h := by
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
  change j x ≫ toProjOn L q d s hd U hU = j x ≫ (U.ι ≫ toProj L q h)
  rw [← Category.assoc, show j x ≫ U.ι = (V x).ι from Scheme.homOfLE_ι _ _]
  rw [toProj_comp L q h (V x).ι eV s hd
    (SectionGradedProjChart.ringHom_of_isUnit L (V x) eV s (inf_le_left.trans hU))]
  exact (toProjOn_restrict L q d s hd inf_le_left hU).trans
    (toProjOn_eq_chart L q d s hd (V x) (inf_le_left.trans hU) eV)

end FLT.Mazur.SectionRetainedChartMorphism
