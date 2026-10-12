/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.VariableHilbertFixedBaseProjection
public import FLT.Mazur.VariableHilbertChartRelationOperations

/-!
# The full original relation on localized varying Hilbert charts

The actual relation morphism retains both endpoints. Its universal property
holds on arbitrary test schemes, with independently varying translation
coordinates and without discarding nonreduced tests.
-/

@[expose] public noncomputable section
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry Opposite
namespace FLT.Mazur.HilbertChart
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
local notation "J" => variableChartRelation q h d W c'

/-- Every local full-relation arrow gives an original full-relation arrow. -/
theorem variableChartFixedBase_original_class :
    (relativeFppfSheaf f).obj.map
        ((Over.map a).map (variableChartRelationFst q h d W c') ≫ P).op
        (variableChartSection f hL d V c) =
      (relativeFppfSheaf f).obj.map
        ((Over.map a).map (variableChartRelationSnd q h d W c') ≫ P).op
        (variableChartSection f hL d V c) := by
  rw [variableChartSection_map, variableChartSection_map]
  apply (variableHilbertFixedBaseProjection_eq_iff f a hL d V W t c J _ _).mpr
  simpa only [variableChartSection_map] using variableChartRelation_class q h d W c'

/-- The actual full relation maps to the original full relation, with its original endpoints. -/
def variableChartFixedBaseRelationProjection :
    (Over.map a).obj J ⟶ variableChartRelation f hL d V c :=
  variableChartRelationLift f hL d V c
    ((Over.map a).map (variableChartRelationFst q h d W c') ≫ P)
    ((Over.map a).map (variableChartRelationSnd q h d W c') ≫ P)
    (variableChartFixedBase_original_class f a hL d V W t c)

/-- The first full-relation endpoint is the original chart projection. -/
@[reassoc]
theorem variableChartFixedBaseRelationProjection_fst :
    variableChartFixedBaseRelationProjection f a hL d V W t c ≫
        variableChartRelationFst f hL d V c =
      (Over.map a).map (variableChartRelationFst q h d W c') ≫ P :=
  variableChartRelationLift_fst _ _ _ _ _ _ _ _

/-- The second endpoint retains its separate translation coordinate. -/
@[reassoc]
theorem variableChartFixedBaseRelationProjection_snd :
    variableChartFixedBaseRelationProjection f a hL d V W t c ≫
        variableChartRelationSnd f hL d V c =
      (Over.map a).map (variableChartRelationSnd q h d W c') ≫ P :=
  variableChartRelationLift_snd _ _ _ _ _ _ _ _

/-- Every original relation over local endpoints has a unique full local relation lift. -/
theorem variableChartFixedBaseRelation_lift (T : Over (Spec (.of R')))
    (k l : T ⟶ variableHilbertTest q d W)
    (r : (Over.map a).obj T ⟶ variableChartRelation f hL d V c)
    (hr₁ : r ≫ variableChartRelationFst f hL d V c = (Over.map a).map k ≫ P)
    (hr₂ : r ≫ variableChartRelationSnd f hL d V c = (Over.map a).map l ≫ P) :
    ∃! z : T ⟶ J,
      z ≫ variableChartRelationFst q h d W c' = k ∧
      z ≫ variableChartRelationSnd q h d W c' = l ∧
      (Over.map a).map z ≫ variableChartFixedBaseRelationProjection f a hL d V W t c = r := by
  have hc := congrArg ((relativeFppfSheaf f).obj.map r.op)
    (variableChartRelation_class f hL d V c)
  have ho : variableHilbertPoint f d hL V c ((Over.map a).obj T)
      ((Over.map a).map k ≫ P) =
        variableHilbertPoint f d hL V c ((Over.map a).obj T)
          ((Over.map a).map l ≫ P) := by
    simpa only [variableChartSection_map, ← variableHilbertPoint_natural,
      hr₁, hr₂] using hc
  have hn := (variableHilbertFixedBaseProjection_eq_iff f a hL d V W t c T k l).mp ho
  obtain ⟨z, hz, hu⟩ := variableChartRelation_lift q h d W c' k l
    (by simpa only [variableChartSection_map] using hn)
  refine ⟨z, ⟨hz.1, hz.2, ?_⟩, fun y hy ↦ hu y ⟨hy.1, hy.2.1⟩⟩
  apply variableChartRelation_hom_ext f hL d V c
  · rw [Category.assoc, variableChartFixedBaseRelationProjection_fst,
      ← Category.assoc, ← Functor.map_comp, hz.1, hr₁]
  · rw [Category.assoc, variableChartFixedBaseRelationProjection_snd,
      ← Category.assoc, ← Functor.map_comp, hz.2, hr₂]

end FLT.Mazur.HilbertChart
