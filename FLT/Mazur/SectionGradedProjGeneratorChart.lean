/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.SectionGradedProjChart
public import FLT.Mazur.ModuleSectionRatioOpen

/-!
# Proj charts on actual generator opens

The unit-coordinate condition follows from the actual section morphism being
invertible. Consequently the local Proj map is defined on a subopen of the
canonical generator open whenever the original line bundle is trivial there.
-/

@[expose] public noncomputable section
open CategoryTheory AlgebraicGeometry
open Scheme.Modules
namespace FLT.Mazur.SectionGradedProjChart
open FCurve ModuleLineBundleTensorPullback SectionGradedSum SectionGradedCoordinates
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
variable {X : Scheme}

/-- An actual global generator has unit coordinate in every sheaf trivialization. -/
lemma coordinate_isUnit_of_generator (M : X.Modules) (s : Γ(M, ⊤))
    (e : M ≅ structureModule X) [IsIso (globalSectionHom M s)] :
    IsUnit (show Γ(X, ⊤) from e.hom.app ⊤ s) := by
  have hi : IsIso ((globalSectionHom M s ≫ e.hom).app ⊤) := inferInstance
  obtain ⟨r, hr⟩ := (ConcreteCategory.bijective_of_isIso
    ((globalSectionHom M s ≫ e.hom).app ⊤)).surjective (1 : Γ(X, ⊤))
  change Γ(X, ⊤) at r
  change (show Γ(X, ⊤) from e.hom.app ⊤ ((globalSectionHom M s).app ⊤ r)) = 1 at hr
  have hgr : (globalSectionHom M s).app ⊤ r = r • s := by
    change r • M.presheaf.map (𝟙 _) s = r • s
    rw [M.presheaf.map_id, ConcreteCategory.id_apply]
  rw [hgr, Hom.app_smul] at hr
  exact IsUnit.of_mul_eq_one_right r hr

/-- Pullback to a subopen of the actual generator open retains the generating section. -/
lemma generator_subopen_isIso (M : X.Modules) (s : Γ(M, ⊤)) (U : X.Opens)
    (hU : U ≤ sectionGeneratorOpen M s) :
    IsIso (globalSectionHom _ (pullGlobal U.ι M s)) := by
  have hr : IsIso ((restrictFunctor U.ι).map (globalSectionHom M s)) :=
    (le_moduleHomIsoOpen_iff _ U).mp hU
  have hn := (restrictFunctorIsoPullback U.ι).hom.naturality (globalSectionHom M s)
  have hp : IsIso ((restrictFunctorIsoPullback U.ι).hom.app (structureModule X) ≫
      (pullback U.ι).map (globalSectionHom M s)) := by
    rw [← hn]
    infer_instance
  have : IsIso ((pullback U.ι).map (globalSectionHom M s)) :=
    IsIso.of_isIso_comp_left ((restrictFunctorIsoPullback U.ι).hom.app (structureModule X)) _
  exact (globalSectionHom_pullGlobal_isIso_iff U.ι M s).mpr inferInstance

variable (L : X.Modules) [Fact (LocallyFreeRankOne L)] (U : X.Opens)
  (e : (pullback U.ι).obj L ≅ structureModule U.toScheme)

omit [Fact (LocallyFreeRankOne L)] in
/-- A genuine generator of a positive tensor power supplies the chart's unit coordinate. -/
lemma ringHom_of_isUnit {d : ℕ} (s : Γ(tensorPower L d, ⊤))
    (hU : U ≤ sectionGeneratorOpen (tensorPower L d) s) :
    IsUnit (ringHom U.ι L e (of L ⊤ d s)) := by
  have := generator_subopen_isIso (tensorPower L d) s U hU
  have := globalSectionHom_isIso_transport _ (tensorPowerIso U.ι L d)
    (pullGlobal U.ι (tensorPower L d) s)
  rw [ringHom_of]
  change IsUnit (show Γ(U.toScheme, ⊤) from (tensorPowerTrivialization e d).hom.app ⊤
    ((tensorPowerIso U.ι L d).hom.app ⊤ (pullGlobal U.ι (tensorPower L d) s)))
  exact coordinate_isUnit_of_generator _ _ (tensorPowerTrivialization e d)

/-- The actual map on a trivializing subopen of a positive-degree section's generator open. -/
def generatorChart {d : ℕ} (s : Γ(tensorPower L d, ⊤)) (hd : 0 < d)
    (hU : U ≤ sectionGeneratorOpen (tensorPower L d) s) : U.toScheme ⟶ Proj (grade L ⊤) :=
  toProj U.ι L e (of L ⊤ d s) (ringHom_of_isUnit L U e s hU) ⟨s, rfl⟩ hd

/-- Changing the trivialization does not change the map on an actual generator subopen. -/
lemma generatorChart_independent (e' : (pullback U.ι).obj L ≅ structureModule U.toScheme)
    {d : ℕ} (s : Γ(tensorPower L d, ⊤)) (hd : 0 < d)
    (hU : U ≤ sectionGeneratorOpen (tensorPower L d) s) :
    generatorChart L U e s hd hU = generatorChart L U e' s hd hU :=
  toProj_independent U.ι L e e' _ _ _ _ _

/-- Different generating positive-degree sections give the same map on their common subopen. -/
lemma generatorChart_eq {d n : ℕ} (s : Γ(tensorPower L d, ⊤)) (t : Γ(tensorPower L n, ⊤))
    (hd : 0 < d) (hn : 0 < n)
    (hs : U ≤ sectionGeneratorOpen (tensorPower L d) s)
    (ht : U ≤ sectionGeneratorOpen (tensorPower L n) t) :
    generatorChart L U e s hd hs = generatorChart L U e t hn ht :=
  toProj_eq U.ι L e _ _ _ _ _ hd _ hn

end FLT.Mazur.SectionGradedProjChart
