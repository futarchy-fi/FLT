/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.AffineFreeSectionLineComparison
public import FLT.Mazur.FiniteFreeChartSectionLinePullback

/-!
# Coherent specified lines in the original finite free charts

Image equalities for the original chart transitions construct comparisons
preserving the original ambient inclusion. Their cocycle uses the genuine
three-chart transition, and survives pullback to every test scheme.
-/

@[expose] public noncomputable section
open CategoryTheory AlgebraicGeometry
open Scheme.Modules
universe u
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
namespace FLT.Mazur.FiniteFreeChartTransitions
open AffineFreeSheafCoordinates NormalizedSectionLine FiniteFreeContragredient
variable {X : Scheme.{u}} (M : X.Modules)
variable {U V Z W : X.Opens} [IsAffine W.toScheme]
variable (hU : W ≤ U) (hV : W ≤ V) (hZ : W ≤ Z)
variable {ι κ ν : Type u} [Finite ι] [Finite κ] [Finite ν]
variable (e : M.restrict U.ι ≅ SheafOfModules.free ι)
variable (d : M.restrict V.ι ≅ SheafOfModules.free κ)
variable (c : M.restrict Z.ι ≅ SheafOfModules.free ν)

/-- Compare specified lines using the actual image equality on a common affine refinement. -/
def chartSectionLineCompare (i : ι) (j : κ)
    (L : Chart Γ(W.toScheme, ⊤) ι i) (N : Chart Γ(W.toScheme, ⊤) κ j)
    (h : L.val.map (functionCoordinates
      (coordinates W.toScheme (transition M hU hV e d))).toLinearMap = N.val) :
    sectionLineSheaf W.toScheme i L ≅ sectionLineSheaf W.toScheme j N :=
  sectionLineCompare W.toScheme (transition M hU hV e d) i j L N h

/-- The constructed comparison preserves the inclusion in the original module sheaf. -/
lemma chartSectionLineCompare_inclusion (i : ι) (j : κ)
    (L : Chart Γ(W.toScheme, ⊤) ι i) (N : Chart Γ(W.toScheme, ⊤) κ j) (h) :
    (chartSectionLineCompare M hU hV e d i j L N h).hom ≫
      chartSectionLineInclusion M hV d j N = chartSectionLineInclusion M hU e i L := by
  dsimp only [chartSectionLineCompare, chartSectionLineInclusion]
  rw [← Category.assoc, sectionLineCompare_inclusion]
  simp only [transition, Iso.trans_hom, Iso.symm_hom, Category.assoc,
    Iso.hom_inv_id, Category.comp_id]

/-- Image equalities compose through the genuine three-chart cocycle. -/
lemma chartSectionLineImage_cocycle (i : ι) (j : κ) (k : ν)
    (L : Chart Γ(W.toScheme, ⊤) ι i) (N : Chart Γ(W.toScheme, ⊤) κ j)
    (P : Chart Γ(W.toScheme, ⊤) ν k)
    (h : L.val.map (functionCoordinates
      (coordinates W.toScheme (transition M hU hV e d))).toLinearMap = N.val)
    (h' : N.val.map (functionCoordinates
      (coordinates W.toScheme (transition M hV hZ d c))).toLinearMap = P.val) :
    L.val.map (functionCoordinates
      (coordinates W.toScheme (transition M hU hZ e c))).toLinearMap = P.val := by
  rw [← transition_cocycle M hU hV hZ e d c]
  exact sectionLineImage_trans W.toScheme _ _ i j k L N P h h'

/-- The comparisons satisfy the cocycle in the original ambient module sheaf. -/
lemma chartSectionLineCompare_cocycle (i : ι) (j : κ) (k : ν)
    (L : Chart Γ(W.toScheme, ⊤) ι i) (N : Chart Γ(W.toScheme, ⊤) κ j)
    (P : Chart Γ(W.toScheme, ⊤) ν k) (h) (h') :
    chartSectionLineCompare M hU hV e d i j L N h ≪≫
        chartSectionLineCompare M hV hZ d c j k N P h' =
      chartSectionLineCompare M hU hZ e c i k L P
        (chartSectionLineImage_cocycle M hU hV hZ e d c i j k L N P h h') := by
  apply Iso.ext
  apply (cancel_mono (chartSectionLineInclusion M hZ c k P)).mp
  simp only [Iso.trans_hom, Category.assoc, chartSectionLineCompare_inclusion]

/-- Each comparison preserves the actual ambient inclusion after any test pullback. -/
lemma chartSectionLineCompare_test_inclusion {T : Scheme.{u}} (f : T ⟶ W.toScheme)
    (i : ι) (j : κ) (L : Chart Γ(W.toScheme, ⊤) ι i)
    (N : Chart Γ(W.toScheme, ⊤) κ j) (h) :
    (pullback f).map (chartSectionLineCompare M hU hV e d i j L N h).hom ≫
        testSectionLineInclusion M hV d f j N = testSectionLineInclusion M hU e f i L := by
  dsimp only [testSectionLineInclusion]
  rw [← Functor.map_comp, chartSectionLineCompare_inclusion]

/-- The original three-chart cocycle persists on arbitrary test schemes. -/
lemma chartSectionLineCompare_test_cocycle {T : Scheme.{u}} (f : T ⟶ W.toScheme)
    (i : ι) (j : κ) (k : ν) (L : Chart Γ(W.toScheme, ⊤) ι i)
    (N : Chart Γ(W.toScheme, ⊤) κ j) (P : Chart Γ(W.toScheme, ⊤) ν k) (h) (h') :
    (pullback f).mapIso (chartSectionLineCompare M hU hV e d i j L N h) ≪≫
        (pullback f).mapIso (chartSectionLineCompare M hV hZ d c j k N P h') =
      (pullback f).mapIso (chartSectionLineCompare M hU hZ e c i k L P
        (chartSectionLineImage_cocycle M hU hV hZ e d c i j k L N P h h')) := by
  rw [← Functor.mapIso_trans, chartSectionLineCompare_cocycle]

end FLT.Mazur.FiniteFreeChartTransitions
