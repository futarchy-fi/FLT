/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.AffineHilbertFixedBaseRelation
public import FLT.Mazur.RelativeRelationMonicBaseLift

/-!
# Inverting the full restricted relation over a monic coefficient base

An isomorphism of the restricted sources and a monic base change recover the
entire original relation, including both independently varying endpoints.
-/

@[expose] public noncomputable section
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry Opposite
namespace FLT.Mazur.HilbertChart.AffineRestriction
open FCurve CartierAbel SchemePicard
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
variable {R R' : Type} [CommRing R] [CommRing R']
  [Algebra.FiniteType ℤ R] [Algebra.FiniteType ℤ R']
  {X : Scheme} (f : X ⟶ Spec (.of R)) (a : Spec (.of R') ⟶ Spec (.of R)) [Mono a]
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
    variableHilbertFixedBaseProjection f a hL d V W t) [IsIso u]

local notation "p" => fst f hL d V c k
local notation "s" => snd f hL d V c k
local notation "p'" => fst q h d W c' l
local notation "s'" => snd q h d W c' l
local notation "x" => MonicBaseRelation.localFst a p (asIso u)
local notation "y" => MonicBaseRelation.localSnd a p s (asIso u)
local notation "i" => MonicBaseRelation.originalIso a p (asIso u)

include hu in
/-- The original relation, with its lifted base, has equal localized classes. -/
theorem fixedBaseInverse_class :
    (relativeFppfSheaf q).obj.map (x).op (sectionAt q h d W c' l) =
      (relativeFppfSheaf q).obj.map (y).op (sectionAt q h d W c' l) := by
  apply (fixedBase_section_eq_iff f a hL d V W t c k l u hu x y).mp
  rw [show (Over.map a).map x ≫ u = (i).hom ≫ p from
    MonicBaseRelation.localFst_original a p (asIso u)]
  rw [show (Over.map a).map y ≫ u = (i).hom ≫ s from
    MonicBaseRelation.localSnd_original a p s (asIso u)]
  exact equal_class_natural f hL d V c k (i).hom

/-- The actual original restricted arrow has a local inverse with both endpoints retained. -/
def fixedBaseRelationInverse :
    relation f hL d V c k ⟶ (Over.map a).obj (relation q h d W c' l) :=
  (i).inv ≫ (Over.map a).map (arrow q h d W c' l x y
    (fixedBaseInverse_class f a hL d V W t c k l u hu))

/-- The inverse recovers the first original endpoint. -/
@[reassoc]
theorem fixedBaseRelationInverse_fst :
    fixedBaseRelationInverse f a hL d V W t c k l u hu ≫ (Over.map a).map p' ≫ u = p := by
  rw [fixedBaseRelationInverse, Category.assoc, ← Functor.map_comp_assoc, arrow_fst]
  change (i).inv ≫ (Over.map a).map x ≫ (asIso u).hom = p
  rw [MonicBaseRelation.localFst_original, Iso.inv_hom_id_assoc]

/-- The inverse recovers the independent second original endpoint. -/
@[reassoc]
theorem fixedBaseRelationInverse_snd :
    fixedBaseRelationInverse f a hL d V W t c k l u hu ≫ (Over.map a).map s' ≫ u = s := by
  rw [fixedBaseRelationInverse, Category.assoc, ← Functor.map_comp_assoc, arrow_snd]
  change (i).inv ≫ (Over.map a).map y ≫ (asIso u).hom = s
  rw [MonicBaseRelation.localSnd_original, Iso.inv_hom_id_assoc]

/-- The inverse followed by the original relation map is the identity on original arrows. -/
theorem fixedBaseRelationInverse_map :
    fixedBaseRelationInverse f a hL d V W t c k l u hu ≫
      fixedBaseRelationMap f a hL d V W t c k l u hu = 𝟙 _ := by
  apply hom_ext f hL d V c k
  · rw [Category.assoc, fixedBaseRelationMap_fst, fixedBaseRelationInverse_fst,
      Category.id_comp]
  · rw [Category.assoc, fixedBaseRelationMap_snd, fixedBaseRelationInverse_snd,
      Category.id_comp]

/-- The other composite is the identity on every local original arrow. -/
theorem fixedBaseRelationMap_inverse :
    fixedBaseRelationMap f a hL d V W t c k l u hu ≫
      fixedBaseRelationInverse f a hL d V W t c k l u hu = 𝟙 _ := by
  let z := fixedBaseRelationMap f a hL d V W t c k l u hu ≫
    fixedBaseRelationInverse f a hL d V W t c k l u hu
  let z' : relation q h d W c' l ⟶ relation q h d W c' l :=
    Over.homMk z.left (by
      apply (cancel_mono a).mp
      simpa only [Over.map_obj_hom, Category.assoc] using Over.w z)
  have hz : z' = 𝟙 _ := by
    apply hom_ext q h d W c' l
    · apply Over.OverMorphism.ext
      apply (cancel_mono u.left).mp
      have hh : z ≫ (Over.map a).map p' ≫ u = (Over.map a).map p' ≫ u := by
        dsimp only [z]
        rw [Category.assoc, fixedBaseRelationInverse_fst, fixedBaseRelationMap_fst]
      exact congrArg Over.Hom.left hh
    · apply Over.OverMorphism.ext
      apply (cancel_mono u.left).mp
      have hh : z ≫ (Over.map a).map s' ≫ u = (Over.map a).map s' ≫ u := by
        dsimp only [z]
        rw [Category.assoc, fixedBaseRelationInverse_snd, fixedBaseRelationMap_snd]
      exact congrArg Over.Hom.left hh
  apply Over.OverMorphism.ext
  have hh := congrArg Over.Hom.left hz
  exact hh

/-- Monic coefficient localization gives an isomorphism of the FULL original relations. -/
def fixedBaseRelationIso :
    (Over.map a).obj (relation q h d W c' l) ≅ relation f hL d V c k where
  hom := fixedBaseRelationMap f a hL d V W t c k l u hu
  inv := fixedBaseRelationInverse f a hL d V W t c k l u hu
  hom_inv_id := fixedBaseRelationMap_inverse f a hL d V W t c k l u hu
  inv_hom_id := fixedBaseRelationInverse_map f a hL d V W t c k l u hu

end FLT.Mazur.HilbertChart.AffineRestriction
