/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.AffineFreeSectionLineTransport

/-!
# Section lines in the original finite free sheaf charts

Changing actual free charts transports a normalized line to the same sheaf
subobject of the original module sheaf. The scheme point classified by the
transported line is its image under the genuine dual projective transition.
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

/-- The original free chart includes the actual line in the original restricted module sheaf. -/
def chartSectionLineInclusion (i : ι) (L : Chart Γ(W.toScheme, ⊤) ι i) :
    sectionLineSheaf W.toScheme i L ⟶ M.restrict W.ι :=
  sectionLineInclusion W.toScheme i L ≫ (refineChart M hU e).inv

instance (i : ι) (L : Chart Γ(W.toScheme, ⊤) ι i) :
    Mono (chartSectionLineInclusion M hU e i L) := by
  dsimp only [chartSectionLineInclusion]
  infer_instance

/-- The original coordinate transition transports the genuine normalized section submodule. -/
def chartSectionLineTransport (i : ι) (j : κ) (L : Chart Γ(W.toScheme, ⊤) ι i)
    (a : Γ(W.toScheme, ⊤)ˣ)
    (ha : functionCoordinates (coordinates W.toScheme (transition M hU hV e d))
      (generator Γ(W.toScheme, ⊤) ι i L) j = a) : Chart Γ(W.toScheme, ⊤) κ j :=
  linearTransport (functionCoordinates (coordinates W.toScheme (transition M hU hV e d)))
    i j L a ha

/-- Its value is the image of the original submodule under the original section coordinates. -/
lemma chartSectionLineTransport_val (i : ι) (j : κ) (L : Chart Γ(W.toScheme, ⊤) ι i)
    (a : Γ(W.toScheme, ⊤)ˣ) (ha) :
    (chartSectionLineTransport M hU hV e d i j L a ha).val = L.val.map
      (functionCoordinates (coordinates W.toScheme (transition M hU hV e d))).toLinearMap := rfl

/-- The actual line sheaves are compared by the original recovered coordinate isomorphism. -/
def chartSectionLineIso (i : ι) (j : κ) (L : Chart Γ(W.toScheme, ⊤) ι i)
    (a : Γ(W.toScheme, ⊤)ˣ) (ha) :
    sectionLineSheaf W.toScheme i L ≅
      sectionLineSheaf W.toScheme j (chartSectionLineTransport M hU hV e d i j L a ha) :=
  sectionLineTransport W.toScheme (transition M hU hV e d) i j L a ha

/-- Chart transition preserves the actual inclusion in the original module sheaf. -/
lemma chartSectionLineIso_inclusion (i : ι) (j : κ) (L : Chart Γ(W.toScheme, ⊤) ι i)
    (a : Γ(W.toScheme, ⊤)ˣ) (ha) :
    (chartSectionLineIso M hU hV e d i j L a ha).hom ≫
        chartSectionLineInclusion M hV d j
          (chartSectionLineTransport M hU hV e d i j L a ha) =
      chartSectionLineInclusion M hU e i L := by
  dsimp only [chartSectionLineIso, chartSectionLineInclusion, chartSectionLineTransport]
  rw [← Category.assoc, sectionLineTransport_inclusion]
  simp only [transition, Iso.trans_hom, Iso.symm_hom, Category.assoc,
    Iso.hom_inv_id, Category.comp_id]

/-- The original module-sheaf inclusion determines this chart comparison uniquely. -/
lemma chartSectionLineIso_unique (i : ι) (j : κ) (L : Chart Γ(W.toScheme, ⊤) ι i)
    (a : Γ(W.toScheme, ⊤)ˣ) (ha)
    (f : sectionLineSheaf W.toScheme i L ⟶
      sectionLineSheaf W.toScheme j (chartSectionLineTransport M hU hV e d i j L a ha))
    (hf : f ≫ chartSectionLineInclusion M hV d j
      (chartSectionLineTransport M hU hV e d i j L a ha) =
        chartSectionLineInclusion M hU e i L) :
    f = (chartSectionLineIso M hU hV e d i j L a ha).hom := by
  apply (cancel_mono (chartSectionLineInclusion M hV d j _)).mp
  rw [hf, chartSectionLineIso_inclusion]

/-- The classified scheme point changes by the actual dual projective chart transition. -/
lemma chartSectionLineTransport_point (i : ι) (j : κ) (L : Chart Γ(W.toScheme, ⊤) ι i)
    (a : Γ(W.toScheme, ⊤)ˣ) (ha) :
    sectionLinePoint Γ(W.toScheme, ⊤) ι (.id _) i L ≫
        (dualProjectiveTransition M hU hV e d).hom =
      sectionLinePoint Γ(W.toScheme, ⊤) κ (.id _) j
        (chartSectionLineTransport M hU hV e d i j L a ha) :=
  sectionLinePoint_linearTransport _ i j L a ha

end FLT.Mazur.FiniteFreeChartTransitions
