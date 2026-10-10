/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.DualAtlasGeometricSectionPullback
public import FLT.Mazur.DualAtlasLineQuotient

/-!
# A universal retained line on the actual dual projective atlas

The cartesian atlas square identifies morphisms over the original base with
sections of the pulled atlas. Apply this to its identity morphism, then use
the proved geometric section-to-line construction. This gives an actual
locally split rank-one sheaf in the pulled original ambient bundle.
-/

@[expose] public noncomputable section
open CategoryTheory AlgebraicGeometry
open Scheme.Modules
universe u
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
namespace FLT.Mazur.DualAtlasUniversalLine
open FCurve DualAtlasLineQuotient LocallyFreeDualProjectiveAtlas
variable {S T : Scheme.{u}} (M : S.Modules) (hM : LocallyFiniteFree M) (g : T ⟶ S)

/-- Lift an actual morphism to the original atlas using its cartesian base-change square. -/
@[irreducible] def sectionOfMorphism (a : T ⟶ space M hM) (ha : a ≫ projection M hM = g) :
    Section ((pullback g).obj M) (hM.pullback g) :=
  ⟨(DualAtlasBaseChangeCharts.map_isPullback g M hM).lift a (𝟙 T)
    (by simpa only [Category.id_comp] using ha),
    (DualAtlasBaseChangeCharts.map_isPullback g M hM).lift_snd _ _ _⟩

/-- The lift retains its independently given original atlas morphism. -/
@[reassoc]
lemma sectionOfMorphism_map (a : T ⟶ space M hM) (ha : a ≫ projection M hM = g) :
    (sectionOfMorphism M hM g a ha).val ≫ DualAtlasBaseChangeCharts.map g M hM = a := by
  unfold sectionOfMorphism
  exact (DualAtlasBaseChangeCharts.map_isPullback g M hM).lift_fst _ _ _

/-- Return from a pulled atlas section to its actual original-base morphism. -/
def morphismOfSection (s : Section ((pullback g).obj M) (hM.pullback g)) :
    {a : T ⟶ space M hM // a ≫ projection M hM = g} :=
  ⟨s.val ≫ DualAtlasBaseChangeCharts.map g M hM, by
    rw [Category.assoc, DualAtlasBaseChangeCharts.map_projection,
      ← Category.assoc, s.property, Category.id_comp]⟩

/-- The actual cartesian atlas represents morphisms over any test base by pulled sections. -/
def morphismSectionEquiv : {a : T ⟶ space M hM // a ≫ projection M hM = g} ≃
    Section ((pullback g).obj M) (hM.pullback g) where
  toFun a := sectionOfMorphism M hM g a.val a.property
  invFun := morphismOfSection M hM g
  left_inv a := Subtype.ext (sectionOfMorphism_map M hM g a.val a.property)
  right_inv s := by
    apply Subtype.ext
    apply (DualAtlasBaseChangeCharts.map_isPullback g M hM).hom_ext
    · exact sectionOfMorphism_map M hM g _ _
    · exact (sectionOfMorphism M hM g _ _).property.trans s.property.symm

/-- The identity of the original atlas determines its universal pulled-atlas section. -/
@[irreducible] def universalSection :
    Section ((pullback (projection M hM)).obj M) (hM.pullback (projection M hM)) :=
  sectionOfMorphism M hM (projection M hM) (𝟙 _) (Category.id_comp _)

/-- The universal section lies above the identity of the original atlas scheme. -/
lemma universalSection_map :
    (universalSection M hM).val ≫
      DualAtlasBaseChangeCharts.map (projection M hM) M hM = 𝟙 _ := by
  unfold universalSection
  exact sectionOfMorphism_map M hM _ _ _

/-- The universal retained line is constructed by geometric forward recovery. -/
@[irreducible] def universalLine : Line ((pullback (projection M hM)).obj M) :=
  fromSection _ (hM.pullback (projection M hM)) (universalSection M hM)

/-- The constructed retained line recovers the actual universal geometric section. -/
lemma universalLine_section :
    toSection _ (hM.pullback (projection M hM)) (universalLine M hM) =
      universalSection M hM := by
  unfold universalLine
  exact toSection_fromSection _ _ _

/-- The atlas map of the actual universal inclusion recovers the original identity. -/
lemma universalLine_map :
    (toSection _ (hM.pullback (projection M hM)) (universalLine M hM)).val ≫
      DualAtlasBaseChangeCharts.map (projection M hM) M hM = 𝟙 _ := by
  rw [universalLine_section, universalSection_map]

end FLT.Mazur.DualAtlasUniversalLine
