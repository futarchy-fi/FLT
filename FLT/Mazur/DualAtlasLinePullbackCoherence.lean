/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.DualAtlasSectionTransport
public import FLT.Mazur.SheafPullbackPathComparison

/-!
# Coherence of the actual retained line under pullback

Pullback preserves original source isomorphisms. The geometric composition
comparison identifies iterated inclusions with the inclusion over the composite.
-/

@[expose] public noncomputable section
open CategoryTheory AlgebraicGeometry
open Scheme.Modules
universe u
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
namespace FLT.Mazur.DualAtlasLineQuotient
variable {X Y Z : Scheme.{u}} {M N : Z.Modules}

/-- Pullback preserves the isomorphism relation on the original retained source lines. -/
lemma baseChange_respects (g : Y ⟶ Z) (a b : Line M) (h : (lineSetoid M).r a b) :
    (lineSetoid ((pullback g).obj M)).r (a.baseChange g) (b.baseChange g) := by
  obtain ⟨e, he⟩ := h
  refine ⟨(pullback g).mapIso e, ?_⟩
  change (pullback g).map e.hom ≫ (pullback g).map b.inclusion =
    (pullback g).map a.inclusion
  rw [← Functor.map_comp, he]

/-- Pulling the original ambient isomorphism commutes with transport of the retained line. -/
lemma baseChange_changeAmbient (g : Y ⟶ Z) (a : Line M) (e : M ≅ N) :
    (a.changeAmbient e).baseChange g =
      (a.baseChange g).changeAmbient ((pullback g).mapIso e) := by
  simp only [Line.baseChange, Line.changeAmbient, Functor.map_comp, Functor.mapIso_hom]

variable (f : X ⟶ Y) (g : Y ⟶ Z) (k : X ⟶ Z) (w : f ≫ g = k) (a : Line M)

/-- The actual source comparison for a normalized two-step geometric pullback. -/
def Line.pathIso : ((a.baseChange g).baseChange f).source ≅ (a.baseChange k).source :=
  (SheafPullbackPathComparison.comparison f g k w).app a.source

/-- Source and ambient normalization preserve the independently pulled original inclusion. -/
lemma Line.pathIso_inclusion :
    (a.pathIso f g k w).hom ≫ (a.baseChange k).inclusion =
      ((a.baseChange g).baseChange f).inclusion ≫
        (SheafPullbackPathComparison.comparison f g k w).hom.app M :=
  ((SheafPullbackPathComparison.comparison f g k w).hom.naturality a.inclusion).symm

/-- Genuine composition, including its ambient comparison, preserves the original line class. -/
lemma baseChange_path_related :
    (lineSetoid ((pullback k).obj M)).r
      (((a.baseChange g).baseChange f).changeAmbient
        ((SheafPullbackPathComparison.comparison f g k w).app M))
      (a.baseChange k) :=
  ⟨a.pathIso f g k w, a.pathIso_inclusion f g k w⟩

end FLT.Mazur.DualAtlasLineQuotient
