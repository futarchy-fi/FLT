/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.FiniteFreeChartSectionLines

/-!
# Actual chart line comparisons on arbitrary test schemes

Pullback of the original chart line inclusion stays split over every test
scheme, without a flatness assumption. The original chart comparison pulls
back to the unique isomorphism preserving inclusion in the actual ambient
module sheaf on that test scheme.
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
variable {U V W : X.Opens} [IsAffine W.toScheme]
variable (hU : W ≤ U) (hV : W ≤ V) {ι κ : Type u} [Finite ι] [Finite κ]
variable (e : M.restrict U.ι ≅ SheafOfModules.free ι)
variable (d : M.restrict V.ι ≅ SheafOfModules.free κ)

instance (i : ι) (L : Chart Γ(W.toScheme, ⊤) ι i) :
    IsSplitMono (chartSectionLineInclusion M hU e i L) := by
  refine IsSplitMono.mk' ⟨(refineChart M hU e).hom ≫
    CategoryTheory.retraction (sectionLineInclusion W.toScheme i L), ?_⟩
  simp only [chartSectionLineInclusion, Category.assoc, Iso.inv_hom_id_assoc, IsSplitMono.id]

variable {T : Scheme.{u}} (f : T ⟶ W.toScheme)

/-- The original ambient line inclusion pulled back to an arbitrary test scheme. -/
def testSectionLineInclusion (i : ι) (L : Chart Γ(W.toScheme, ⊤) ι i) :
    (pullback f).obj (sectionLineSheaf W.toScheme i L) ⟶
      (pullback f).obj (M.restrict W.ι) :=
  (pullback f).map (chartSectionLineInclusion M hU e i L)

instance (i : ι) (L : Chart Γ(W.toScheme, ⊤) ι i) :
    IsSplitMono (testSectionLineInclusion M hU e f i L) := by
  dsimp only [testSectionLineInclusion]
  infer_instance

/-- The genuine chart comparison pulled back to the test scheme. -/
def testSectionLineIso (i : ι) (j : κ) (L : Chart Γ(W.toScheme, ⊤) ι i)
    (a : Γ(W.toScheme, ⊤)ˣ) (ha) :
    (pullback f).obj (sectionLineSheaf W.toScheme i L) ≅
      (pullback f).obj (sectionLineSheaf W.toScheme j
        (chartSectionLineTransport M hU hV e d i j L a ha)) :=
  (pullback f).mapIso (chartSectionLineIso M hU hV e d i j L a ha)

/-- The comparison preserves the actual ambient inclusion on every test scheme. -/
lemma testSectionLineIso_inclusion (i : ι) (j : κ) (L : Chart Γ(W.toScheme, ⊤) ι i)
    (a : Γ(W.toScheme, ⊤)ˣ) (ha) :
    (testSectionLineIso M hU hV e d f i j L a ha).hom ≫
        testSectionLineInclusion M hV d f j
          (chartSectionLineTransport M hU hV e d i j L a ha) =
      testSectionLineInclusion M hU e f i L := by
  dsimp only [testSectionLineIso, testSectionLineInclusion, Functor.mapIso_hom]
  rw [← Functor.map_comp, chartSectionLineIso_inclusion]

/-- The split ambient inclusion determines the test-scheme comparison uniquely. -/
lemma testSectionLineIso_unique (i : ι) (j : κ) (L : Chart Γ(W.toScheme, ⊤) ι i)
    (a : Γ(W.toScheme, ⊤)ˣ) (ha)
    (g : (pullback f).obj (sectionLineSheaf W.toScheme i L) ⟶
      (pullback f).obj (sectionLineSheaf W.toScheme j
        (chartSectionLineTransport M hU hV e d i j L a ha)))
    (hg : g ≫ testSectionLineInclusion M hV d f j
      (chartSectionLineTransport M hU hV e d i j L a ha) =
        testSectionLineInclusion M hU e f i L) :
    g = (testSectionLineIso M hU hV e d f i j L a ha).hom := by
  apply (cancel_mono (testSectionLineInclusion M hV d f j _)).mp
  rw [hg, testSectionLineIso_inclusion]

end FLT.Mazur.FiniteFreeChartTransitions
