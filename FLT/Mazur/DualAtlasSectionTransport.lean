/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.DualAtlasLineQuotient
public import FLT.Mazur.DualAtlasGeometricSectionPullback

/-!
# Transport of actual atlas sections along ambient isomorphisms and base change

Ambient transport retains the original source and composes its inclusion
with the given sheaf isomorphism. Base pullback uses the cartesian atlas
square, with its value on original line inclusions proved independently.
-/

@[expose] public noncomputable section
open CategoryTheory AlgebraicGeometry
open Scheme.Modules
universe u
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
namespace FLT.Mazur.DualAtlasLineQuotient
open FCurve SplitLineAffineNeighborhood
variable {X Y : Scheme.{u}} {M N : X.Modules}

/-- Transport the actual original line inclusion into an isomorphic ambient bundle. -/
def Line.changeAmbient (e : M ≅ N) (a : Line M) : Line N :=
  ⟨a.source, a.rankOne, a.inclusion ≫ e.hom, a.locallySplit.postcompose a.inclusion e⟩

/-- Ambient transport preserves the retained source-isomorphism relation. -/
lemma changeAmbient_respects (e : M ≅ N) (a b : Line M) (h : (lineSetoid M).r a b) :
    (lineSetoid N).r (a.changeAmbient e) (b.changeAmbient e) := by
  obtain ⟨i, hi⟩ := h
  exact ⟨i, by change i.hom ≫ (b.inclusion ≫ e.hom) = a.inclusion ≫ e.hom
               rw [← Category.assoc, hi]⟩

/-- Ambient isomorphism transport of an actual geometric atlas section. -/
def sectionChangeAmbient (e : M ≅ N) (hM : LocallyFiniteFree M) (hN : LocallyFiniteFree N)
    (s : Section M hM) : Section N hN :=
  toSection N hN ((fromSection M hM s).changeAmbient e)

/-- Transport uses the given ambient isomorphism on every original line inclusion. -/
lemma sectionChangeAmbient_toSection (e : M ≅ N)
    (hM : LocallyFiniteFree M) (hN : LocallyFiniteFree N) (a : Line M) :
    sectionChangeAmbient e hM hN (toSection M hM a) =
      toSection N hN (a.changeAmbient e) := by
  apply (toSection_eq_iff N hN _ _).mpr
  apply changeAmbient_respects
  exact (toSection_eq_iff M hM _ _).mp (toSection_fromSection M hM (toSection M hM a))

/-- Pull the original source line and its locally split inclusion along the base map. -/
def Line.baseChange (g : Y ⟶ X) (a : Line M) : Line ((pullback g).obj M) :=
  ⟨(pullback g).obj a.source, a.rankOne.pullback g,
    (pullback g).map a.inclusion, a.locallySplit.pullback a.inclusion g⟩

/-- Pullback of actual atlas sections uses the geometric cartesian square. -/
def sectionBaseChange (g : Y ⟶ X) (hM : LocallyFiniteFree M) (s : Section M hM) :
    Section ((pullback g).obj M) (hM.pullback g) :=
  ⟨DualAtlasBaseChangeCharts.sectionPullback g M hM s.val s.property,
    DualAtlasBaseChangeCharts.sectionPullback_projection g M hM s.val s.property⟩

/-- Geometric section pullback agrees with pulling the original sheaf inclusion. -/
lemma sectionBaseChange_toSection (g : Y ⟶ X) (hM : LocallyFiniteFree M) (a : Line M) :
    sectionBaseChange g hM (toSection M hM a) =
      toSection ((pullback g).obj M) (hM.pullback g) (a.baseChange g) :=
  Subtype.ext (DualAtlasBaseChangeCharts.sectionPullback_reverse g M hM a.inclusion
    a.rankOne a.locallySplit).symm

end FLT.Mazur.DualAtlasLineQuotient
