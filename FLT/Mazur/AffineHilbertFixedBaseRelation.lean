/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.VariableHilbertFixedBaseRelation
public import FLT.Mazur.AffineHilbertFullRelationRestriction

/-!
# The original restricted relation across coefficient bases

Compatible source restrictions induce an actual map of full relations. Every
original arrow with specified local endpoints has a unique local lift. The
endpoints remain independent and all scheme-valued tests are retained.
-/

@[expose] public noncomputable section
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry Opposite
namespace FLT.Mazur.HilbertChart.AffineRestriction
open FCurve CartierAbel SchemePicard
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
variable {R R' : Type} [CommRing R] [CommRing R']
  [Algebra.FiniteType ℤ R] [Algebra.FiniteType ℤ R']
  {X : Scheme} (f : X ⟶ Spec (.of R)) (a : Spec (.of R') ⟶ Spec (.of R))
  [IsProper f] [Flat f] [GeometricallyIntegral f] [SmoothOfRelativeDimension 1 f]
  {L : X.Modules} (hL : AmpleLineBundle L) (d : ℕ)
  (V : Over (Spec (.of R))) (W : Over (Spec (.of R')))
  (t : (Over.map a).obj W ⟶ V) (c : (relativeFppfSheaf f).obj.obj (op V))
local notation "q" => Limits.pullback.snd f a
local instance : SmoothOfRelativeDimension 1 q :=
  MorphismProperty.pullback_snd _ _ inferInstance
local notation "h" => fixedBaseAmple f a hL
local notation "c'" => fixedBaseTranslationClass f a V W t c
local notation "P" => variableHilbertFixedBaseProjection f a hL d V W t
variable {A : Over (Spec (.of R))} {B : Over (Spec (.of R'))}
  (k : A ⟶ variableHilbertTest f d V) (l : B ⟶ variableHilbertTest (Limits.pullback.snd f a) d W)
  (u : (Over.map a).obj B ⟶ A) (hu : u ≫ k = (Over.map a).map l ≫
    variableHilbertFixedBaseProjection f a hL d V W t)

include hu in
/-- Restricted original class equality is reflected on every local test. -/
theorem fixedBase_section_eq_iff {T : Over (Spec (.of R'))} (x y : T ⟶ B) :
    (relativeFppfSheaf f).obj.map ((Over.map a).map x ≫ u).op
        (sectionAt f hL d V c k) =
      (relativeFppfSheaf f).obj.map ((Over.map a).map y ≫ u).op
        (sectionAt f hL d V c k) ↔
    (relativeFppfSheaf q).obj.map x.op (sectionAt q h d W c' l) =
      (relativeFppfSheaf q).obj.map y.op (sectionAt q h d W c' l) := by
  simpa only [sectionAt, variableChartSection_map, ← variableHilbertPoint_natural,
    Category.assoc, hu, ← Functor.map_comp_assoc] using
    variableHilbertFixedBaseProjection_eq_iff f a hL d V W t c T (x ≫ l) (y ≫ l)

/-- The full restricted local relation maps to the ORIGINAL restricted relation. -/
def fixedBaseRelationMap :
    (Over.map a).obj (relation q h d W c' l) ⟶ relation f hL d V c k :=
  arrow f hL d V c k ((Over.map a).map (fst q h d W c' l) ≫ u)
    ((Over.map a).map (snd q h d W c' l) ≫ u)
    ((fixedBase_section_eq_iff f a hL d V W t c k l u hu _ _).mpr
      (equal_class q h d W c' l))

/-- The first endpoint is the prescribed original source map. -/
@[reassoc]
theorem fixedBaseRelationMap_fst :
    fixedBaseRelationMap f a hL d V W t c k l u hu ≫ fst f hL d V c k =
      (Over.map a).map (fst q h d W c' l) ≫ u := arrow_fst _ _ _ _ _ _ _ _ _

/-- The second endpoint retains its independent source coordinate. -/
@[reassoc]
theorem fixedBaseRelationMap_snd :
    fixedBaseRelationMap f a hL d V W t c k l u hu ≫ snd f hL d V c k =
      (Over.map a).map (snd q h d W c' l) ≫ u := arrow_snd _ _ _ _ _ _ _ _ _

/-- Forgetting restrictions commutes with the already constructed full-relation projection. -/
theorem fixedBaseRelationMap_full :
    fixedBaseRelationMap f a hL d V W t c k l u hu ≫ toFullRelation f hL d V c k =
      (Over.map a).map (toFullRelation q h d W c' l) ≫
        variableChartFixedBaseRelationProjection f a hL d V W t c := by
  apply variableChartRelation_hom_ext f hL d V c
  · simp only [Category.assoc, toFullRelation_fst, fixedBaseRelationMap_fst_assoc,
      variableChartFixedBaseRelationProjection_fst, ← Functor.map_comp_assoc, hu]
  · simp only [Category.assoc, toFullRelation_snd, fixedBaseRelationMap_snd_assoc,
      variableChartFixedBaseRelationProjection_snd, ← Functor.map_comp_assoc, hu]

/-- Every original restricted arrow with local endpoints has a unique full local lift. -/
theorem fixedBaseRelationMap_lift {T : Over (Spec (.of R'))} (x y : T ⟶ B)
    (r : (Over.map a).obj T ⟶ relation f hL d V c k)
    (hr₁ : r ≫ fst f hL d V c k = (Over.map a).map x ≫ u)
    (hr₂ : r ≫ snd f hL d V c k = (Over.map a).map y ≫ u) :
    ∃! z : T ⟶ relation q h d W c' l,
      z ≫ fst q h d W c' l = x ∧ z ≫ snd q h d W c' l = y ∧
      (Over.map a).map z ≫ fixedBaseRelationMap f a hL d V W t c k l u hu = r := by
  have hc := equal_class_natural f hL d V c k r
  rw [hr₁, hr₂] at hc
  obtain ⟨z, hz, hz'⟩ := lift q h d W c' l x y
    ((fixedBase_section_eq_iff f a hL d V W t c k l u hu x y).mp hc)
  refine ⟨z, ⟨hz.1, hz.2, ?_⟩, fun w hw ↦ hz' w ⟨hw.1, hw.2.1⟩⟩
  apply hom_ext f hL d V c k
  · rw [Category.assoc, fixedBaseRelationMap_fst, ← Category.assoc,
      ← Functor.map_comp, hz.1, hr₁]
  · rw [Category.assoc, fixedBaseRelationMap_snd, ← Category.assoc,
      ← Functor.map_comp, hz.2, hr₂]

end FLT.Mazur.HilbertChart.AffineRestriction
