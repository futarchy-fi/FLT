/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.CartierIdealGluedInclusion
public import FLT.Mazur.AffineFaithfullyFlatMonomorphisms
public import FLT.Mazur.SchemeAffineFppfChartCover

/-!
# The descended full ideal inclusion is monic

Flat affine covering charts preserve the source Cartier embedding. Faithful
flatness reflects monicity on the affine base charts, which cover the base.
-/

@[expose] public noncomputable section
open CategoryTheory AlgebraicGeometry
open Scheme.Modules
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
namespace FLT.Mazur.FCurve
open SchemeGeometricDescent SchemeAffineDescent SchemePicard
attribute [local irreducible] ModuleSheafTensor.tensor
variable {X Y : Scheme.{0}} (p : Y ⟶ X)
  [Flat p] [Surjective p] [LocallyOfFinitePresentation p]
  (I : Y.IdealSheafData) (hI : EffectiveCartier I)
  (h : I.comap (Limits.pullback.fst p p) = I.comap (Limits.pullback.snd p p))

/-- Flat refinement of the recovered inclusion retains monicity. -/
lemma cartierIdealGluedInclusion_refined_mono {T : Scheme.{0}} (c : T ⟶ Y) [Flat c] :
    Mono ((pullback c).map ((pullback p).map (cartierIdealGluedInclusion p I hI h))) := by
  let _ := idealModulePullbackHom_isIso_of_flat I hI c
  let _ := idealModulePullbackι_mono I c
  have he := congrArg (fun k ↦ (pullback c).map k ≫ (modulePullbackUnitIso c).hom)
    (cartierIdealGluedInclusion_recovery p I hI h)
  simp only [Functor.map_comp, Category.assoc] at he
  change _ = (pullback c).map (cartierIdealGluedLineIso p I hI h).hom ≫
    idealModulePullbackι I c at he
  exact mono_of_mono_fac he

/-- The inclusion is monic on every constructed affine base chart. -/
lemma cartierIdealGluedInclusion_chart_mono (i : X.affineOpenCover.I₀) :
    Mono ((pullback (fppfCharts p i).base).map
      (cartierIdealGluedInclusion p I hI h)) := by
  let C := fppfCharts p i
  let _ := rankOne_finitePresentation _ ((cartierIdealGluedLine p I hI h).property.pullback
    C.base)
  let _ := rankOne_finitePresentation _ (structureModule_locallyFreeRankOne.pullback C.base)
  let _ := cartierIdealGluedInclusion_refined_mono p I hI h C.cover
  have hn := C.coverPullbackIso.hom.naturality (cartierIdealGluedInclusion p I hI h)
  dsimp only [Functor.comp_map] at hn
  let _ : Mono ((pullback (Spec.map C.ringMap)).map
      ((pullback C.base).map (cartierIdealGluedInclusion p I hI h))) :=
    (mono_comp_iff_of_isIso (C.coverPullbackIso.hom.app _) _).mp (by
      rw [← hn]
      infer_instance)
  exact AffineFaithfullyFlatMonomorphisms.mono_of_pullback C.ringMap C.faithfullyFlat _

/-- The actual global map is an embedding into the structure sheaf. -/
theorem cartierIdealGluedInclusion_mono : Mono (cartierIdealGluedInclusion p I hI h) where
  right_cancellation {M} a b hab := by
    apply ModuleSheafOpenImmersionGluing.hom_ext
      (fun i ↦ Spec (fppfCharts p i).baseRing) (fun i ↦ (fppfCharts p i).base)
      (fun x ↦ by
        obtain ⟨i, y, hy⟩ := X.affineOpenCover.openCover.exists_eq x
        exact ⟨i, y, hy⟩)
    intro i
    let _ := cartierIdealGluedInclusion_chart_mono p I hI h i
    apply (cancel_mono ((pullback (fppfCharts p i).base).map
      (cartierIdealGluedInclusion p I hI h))).mp
    simpa only [Functor.map_comp] using congrArg (pullback (fppfCharts p i).base).map hab

end FLT.Mazur.FCurve
