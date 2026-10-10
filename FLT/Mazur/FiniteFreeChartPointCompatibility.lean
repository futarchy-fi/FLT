/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.FiniteFreeChartSectionLineComparison
public import FLT.Mazur.SectionLinePointOverlapEquality

/-!
# Actual projective point compatibility determines chart line compatibility

On a common affine refinement, equality through the genuine dual projective
transition implies equality of the transported section submodule. A unit
coordinate is needed only to represent the transported line in one chart;
the target point may use any other chart. The resulting sheaf comparison
preserves the original ambient inclusion.
-/

@[expose] public noncomputable section
open CategoryTheory AlgebraicGeometry
open Scheme.Modules
universe u
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
namespace FLT.Mazur.FiniteFreeChartTransitions
open AffineFreeSheafCoordinates NormalizedSectionLine FiniteFreeContragredient ProjectiveSpace
variable {X : Scheme.{u}} (M : X.Modules)
variable {U V W : X.Opens} [IsAffine W.toScheme]
variable (hU : W ≤ U) (hV : W ≤ V) {ι κ : Type u} [Finite ι] [Finite κ]
variable (e : M.restrict U.ι ≅ SheafOfModules.free ι)
variable (d : M.restrict V.ι ≅ SheafOfModules.free κ)

/-- Equality of genuine projective points recovers the actual transported submodule. -/
lemma chartPoint_eq_iff_lineImage (i : ι) (j k : κ)
    (L : Chart Γ(W.toScheme, ⊤) ι i) (N : Chart Γ(W.toScheme, ⊤) κ k)
    (a : Γ(W.toScheme, ⊤)ˣ)
    (ha : functionCoordinates (coordinates W.toScheme (transition M hU hV e d))
      (generator Γ(W.toScheme, ⊤) ι i L) j = a) :
    sectionLinePoint Γ(W.toScheme, ⊤) ι (.id _) i L ≫
        (dualProjectiveTransition M hU hV e d).hom =
      sectionLinePoint Γ(W.toScheme, ⊤) κ (.id _) k N ↔
    L.val.map (functionCoordinates
      (coordinates W.toScheme (transition M hU hV e d))).toLinearMap = N.val := by
  rw [chartSectionLineTransport_point M hU hV e d i j L a ha,
    sectionLinePoint_eq_iff]
  rfl

/-- Compatible actual chart points construct a comparison of their actual line sheaves. -/
def chartPointLineCompare (i : ι) (j k : κ)
    (L : Chart Γ(W.toScheme, ⊤) ι i) (N : Chart Γ(W.toScheme, ⊤) κ k)
    (a : Γ(W.toScheme, ⊤)ˣ)
    (ha : functionCoordinates (coordinates W.toScheme (transition M hU hV e d))
      (generator Γ(W.toScheme, ⊤) ι i L) j = a)
    (hp : sectionLinePoint Γ(W.toScheme, ⊤) ι (.id _) i L ≫
      (dualProjectiveTransition M hU hV e d).hom =
        sectionLinePoint Γ(W.toScheme, ⊤) κ (.id _) k N) :
    sectionLineSheaf W.toScheme i L ≅ sectionLineSheaf W.toScheme k N :=
  chartSectionLineCompare M hU hV e d i k L N
    ((chartPoint_eq_iff_lineImage M hU hV e d i j k L N a ha).mp hp)

/-- The comparison obtained from genuine points preserves the original ambient inclusion. -/
lemma chartPointLineCompare_inclusion (i : ι) (j k : κ)
    (L : Chart Γ(W.toScheme, ⊤) ι i) (N : Chart Γ(W.toScheme, ⊤) κ k)
    (a : Γ(W.toScheme, ⊤)ˣ)
    (ha : functionCoordinates (coordinates W.toScheme (transition M hU hV e d))
      (generator Γ(W.toScheme, ⊤) ι i L) j = a)
    (hp : sectionLinePoint Γ(W.toScheme, ⊤) ι (.id _) i L ≫
      (dualProjectiveTransition M hU hV e d).hom =
        sectionLinePoint Γ(W.toScheme, ⊤) κ (.id _) k N) :
    (chartPointLineCompare M hU hV e d i j k L N a ha hp).hom ≫
      chartSectionLineInclusion M hV d k N = chartSectionLineInclusion M hU e i L :=
  chartSectionLineCompare_inclusion M hU hV e d i k L N _

/-- Compatible actual points give equal subobjects in the original ambient module. -/
lemma chartPoint_subobject_eq (i : ι) (j k : κ)
    (L : Chart Γ(W.toScheme, ⊤) ι i) (N : Chart Γ(W.toScheme, ⊤) κ k)
    (a : Γ(W.toScheme, ⊤)ˣ)
    (ha : functionCoordinates (coordinates W.toScheme (transition M hU hV e d))
      (generator Γ(W.toScheme, ⊤) ι i L) j = a)
    (hp : sectionLinePoint Γ(W.toScheme, ⊤) ι (.id _) i L ≫
      (dualProjectiveTransition M hU hV e d).hom =
        sectionLinePoint Γ(W.toScheme, ⊤) κ (.id _) k N) :
    Subobject.mk (chartSectionLineInclusion M hU e i L) =
      Subobject.mk (chartSectionLineInclusion M hV d k N) :=
  Subobject.mk_eq_mk_of_comm _ _ (chartPointLineCompare M hU hV e d i j k L N a ha hp)
    (chartPointLineCompare_inclusion M hU hV e d i j k L N a ha hp)

end FLT.Mazur.FiniteFreeChartTransitions
