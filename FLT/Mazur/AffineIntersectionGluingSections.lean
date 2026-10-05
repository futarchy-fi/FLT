/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.AffineIntersectionGluingBaseChange
public import FLT.Mazur.IntersectionGluingSections

/-!
# Coordinate rings on the glued affine intersection atlas

Each model algebra identifies with ambient sections on its chart image.
Restriction is precisely the original algebra diagram map, also after
restricting further to an arbitrary subopen of a larger intersection.
-/

@[expose] public noncomputable section

set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry

namespace FLT.Mazur.Approximation

universe u v

variable {S : Type u} [CommRing S] {ι : Type v} [Finite ι]
  (C : NonemptyChartSet ι ⥤ CommAlgCat S)
  [∀ a b (f : a ⟶ b), IsOpenImmersion (Spec.map (CommRingCat.ofHom (C.map f).hom.toRingHom))]

variable [((affineIntersectionSchemeDiagram C) ⋙ Scheme.forget).IsLocallyDirected]

/-- Model coordinates are actual ambient sections on the chart image. -/
def affineIntersectionColimitSectionIso (s : NonemptyChartSet ι) :
    CommRingCat.of (C.obj s) ≅
      Γ(colimit (affineIntersectionSchemeDiagram C),
        intersectionColimitOpen (affineIntersectionSchemeDiagram C) s) :=
  (Scheme.ΓSpecIso (.of (C.obj s))).symm ≪≫
    intersectionColimitSectionIso (affineIntersectionSchemeDiagram C) s

/-- The corresponding ring equivalence, suitable for transporting units. -/
def affineIntersectionColimitSectionEquiv (s : NonemptyChartSet ι) :
    C.obj s ≃+* Γ(colimit (affineIntersectionSchemeDiagram C),
      intersectionColimitOpen (affineIntersectionSchemeDiagram C) s) :=
  (affineIntersectionColimitSectionIso C s).commRingCatIsoToRingEquiv

/-- The comparison intertwines every coordinate map and ambient restriction. -/
theorem affineIntersectionColimitSectionIso_naturality {s t : NonemptyChartSet ι}
    (h : s ≤ t) :
    (affineIntersectionColimitSectionIso C s).hom ≫
        (colimit (affineIntersectionSchemeDiagram C)).presheaf.map
          (homOfLE (intersectionColimitOpen_antitone (affineIntersectionSchemeDiagram C) h)).op =
      CommRingCat.ofHom (C.map (homOfLE h)).hom.toRingHom ≫
        (affineIntersectionColimitSectionIso C t).hom := by
  dsimp only [affineIntersectionColimitSectionIso, Iso.trans_hom, Iso.symm_hom]
  rw [Category.assoc,
    intersectionColimitSectionIso_naturality (affineIntersectionSchemeDiagram C) h]
  change (Scheme.ΓSpecIso _).inv ≫ (Spec.map _).appTop ≫ _ = _
  rw [← Category.assoc, ← Scheme.ΓSpecIso_inv_naturality, Category.assoc]
  rfl

/-- Elementwise restriction compatibility of the coordinate equivalence. -/
theorem affineIntersectionColimitSectionEquiv_naturality {s t : NonemptyChartSet ι}
    (h : s ≤ t) (x : C.obj s) :
    (colimit (affineIntersectionSchemeDiagram C)).presheaf.map
        (homOfLE (intersectionColimitOpen_antitone (affineIntersectionSchemeDiagram C) h)).op
        (affineIntersectionColimitSectionEquiv C s x) =
      affineIntersectionColimitSectionEquiv C t ((C.map (homOfLE h)).hom x) :=
  congrArg (fun f ↦ f x) (affineIntersectionColimitSectionIso_naturality C h)

/-- Coordinates restricted to an arbitrary ambient subopen of a chart. -/
def affineIntersectionSectionToOpen (s : NonemptyChartSet ι)
    (V : (colimit (affineIntersectionSchemeDiagram C)).Opens)
    (h : V ≤ intersectionColimitOpen (affineIntersectionSchemeDiagram C) s) :
    C.obj s →+* Γ(colimit (affineIntersectionSchemeDiagram C), V) :=
  ((colimit (affineIntersectionSchemeDiagram C)).presheaf.map (homOfLE h).op).hom.comp
    (affineIntersectionColimitSectionEquiv C s).toRingHom

/-- Passing through a larger union does not change the resulting ambient section. -/
theorem affineIntersectionSectionToOpen_naturality {s t : NonemptyChartSet ι}
    (h : s ≤ t) (V : (colimit (affineIntersectionSchemeDiagram C)).Opens)
    (hV : V ≤ intersectionColimitOpen (affineIntersectionSchemeDiagram C) t) (x : C.obj s) :
    affineIntersectionSectionToOpen C s V
        (hV.trans (intersectionColimitOpen_antitone (affineIntersectionSchemeDiagram C) h)) x =
      affineIntersectionSectionToOpen C t V hV ((C.map (homOfLE h)).hom x) := by
  change (colimit (affineIntersectionSchemeDiagram C)).presheaf.map _
      (affineIntersectionColimitSectionEquiv C s x) =
    (colimit (affineIntersectionSchemeDiagram C)).presheaf.map _
      (affineIntersectionColimitSectionEquiv C t ((C.map (homOfLE h)).hom x))
  rw [← affineIntersectionColimitSectionEquiv_naturality C h]
  exact congrArg (fun f ↦ f (affineIntersectionColimitSectionEquiv C s x))
    ((colimit (affineIntersectionSchemeDiagram C)).presheaf.map_comp
      (homOfLE (intersectionColimitOpen_antitone (affineIntersectionSchemeDiagram C) h)).op
      (homOfLE hV).op)

end FLT.Mazur.Approximation
