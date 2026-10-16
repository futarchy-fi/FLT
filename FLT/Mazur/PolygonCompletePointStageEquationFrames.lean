/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.AffineDivisorEquationFrame
public import FLT.Mazur.PolygonCompletePointStageBoundedNumerators
public import FLT.Mazur.DivisorLinePullback

/-!
# Specified equation frames at the original full-stage marking

Reconstruct the frame from the original chart equation, then pull it back
along the actual unit-one marking. The original complete pole frame is not
used in constructing this equation frame.
-/

@[expose] public noncomputable section
open CategoryTheory AlgebraicGeometry Scheme.Modules
namespace FLT.Mazur.PolygonInfinitesimalStages
open PolygonSmoothing FCurve ModuleLineBundleTensorPullback
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
attribute [local irreducible] exactVeroneseProj exactVeroneseProjToBase
  originalStageToCompatibleProj ModuleSheafTensor.tensor divisorLineBundle
variable (K : Type) [Field K] (n : ℕ) (h : 2 ≤ n) [NeZero n]
variable (m : ℕ) (i : Fin n)
local notation "t" => parameter K m
local notation "f" => PolygonInfinitesimal.chart (Ring K m) (t) n h i
local notation "q" => markedSection (t) (1 : (Ring K m)ˣ)
local notation "p" => marking K m n h i
local notation "L" => originalStageSinglePointLine K n h m i
local notation "I" => Scheme.Hom.ker (p)
local notation "J" => Scheme.IdealSheafData.comap (I) (f)
local notation "hI" => And.left (originalStageSingleMarking_relativeCartier K n h m i)
local notation "a" => CommRingCat.Hom.hom
  (Iso.inv (Scheme.ΓSpecIso (CommRingCat.of (ChartRing (t)))))
  (PolygonInfinitesimal.chartMarkingEquation (Ring K m) (t) n i i 1)

/-- The chart frame is reconstructed from the original equation, in the original degree. -/
irreducible_def completePointStageChartEquationFrame (d : ℕ) :
    (pullback (f)).obj (tensorPower (L) d) ≅ structureModule (Spec (.of (ChartRing (t)))) := by
  let _ : IsAffine (PolygonSmoothing.chart (Ring K m) (t)) :=
    inferInstanceAs (IsAffine (Spec (.of (ChartRing (t)))))
  exact tensorPowerIso (f) (L) d ≪≫
    tensorPowerCongr (divisorLinePullbackIsoOfEq (f) (hI)
      ((hI).comap_of_isOpenImmersion (f)) rfl) d ≪≫
    divisorEquationPowerFrame ((hI).comap_of_isOpenImmersion (f)) (a)
      (PolygonInfinitesimal.marking_chart_section_regular (Ring K m) (t) n h i i 1)
      (PolygonInfinitesimal.marking_ideal_chart_sections (Ring K m) (t) n h i i 1) d

/-- Pulling back that same equation frame defines the full-stage marking coordinates. -/
irreducible_def completePointStageEquationFrame (d : ℕ) :
    (pullback (p)).obj (tensorPower (L) d) ≅ structureModule (Spec (.of (Ring K m))) :=
  ((pullbackComp (q) (f)).app (tensorPower (L) d)).symm ≪≫
    (pullback (q)).mapIso (completePointStageChartEquationFrame K n h m i d) ≪≫
    modulePullbackUnitIso (q)

/-- A coefficient in the equation frame retains the original section and stage marking. -/
def completePointStageEquationCoefficient (d : ℕ) (s : Γ(tensorPower (L) d, ⊤)) :
    Γ(Spec (.of (Ring K m)), ⊤) :=
  (completePointStageEquationFrame K n h m i d).hom.app ⊤ (pullGlobal (p) _ s)

/-- Equation coefficients are the actual marked pullback of the original chart coordinates. -/
theorem completePointStageEquationCoefficient_chart (d : ℕ)
    (s : Γ(tensorPower (L) d, ⊤)) :
    completePointStageEquationCoefficient K n h m i d s =
      (q).appTop ((completePointStageChartEquationFrame K n h m i d).hom.app ⊤
        (pullGlobal (f) _ s)) := by
  rw [completePointStageEquationCoefficient, completePointStageEquationFrame_def]
  simp only [Iso.trans_hom, Iso.symm_hom, Functor.mapIso_hom,
    Hom.comp_app, ConcreteCategory.comp_apply]
  change (modulePullbackUnitIso (q)).hom.app ⊤
    (((pullback (q)).map (completePointStageChartEquationFrame K n h m i d).hom).app ⊤
      (((pullbackComp (q) (f)).inv.app _).app ⊤ (pullGlobal ((q) ≫ (f)) _ s))) = _
  rw [pullGlobal_comp, pullGlobal_naturality]
  exact modulePullbackUnitIso_unit (q) ⊤ _

end FLT.Mazur.PolygonInfinitesimalStages
