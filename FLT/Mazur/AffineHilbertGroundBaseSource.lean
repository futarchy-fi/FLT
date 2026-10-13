/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.VariableHilbertGroundBaseCartesian
public import FLT.Mazur.AffineHilbertFixedBaseRelation

/-!
# Constructing actual open charts over a changed ground base

Pull back the original source along the genuine Hilbert parameter comparison.
The resulting chart is open, and the source is affine for affine translations.
The proper family and its pulled-back ample bundle remain in the interface.
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
  (t : (Over.map a).obj W ⟶ V)
local notation "q" => Limits.pullback.snd f a
local instance : SmoothOfRelativeDimension 1 q :=
  MorphismProperty.pullback_snd _ _ inferInstance
local notation "P" => variableHilbertFixedBaseProjection f a hL d V W t
variable {A : Over (Spec (.of R))} (k : A ⟶ variableHilbertTest f d V)

/-- The source over the new coefficient ring is an actual scheme pullback. -/
def groundBaseSource : Over (Spec (.of R')) :=
  Over.mk (pullback.snd k.left (P).left ≫ (variableHilbertTest q d W).hom)

/-- The transported Hilbert parameter. -/
def groundBaseSourceChart : groundBaseSource f a hL d V W t k ⟶
    variableHilbertTest q d W := Over.homMk (pullback.snd k.left (P).left) rfl

/-- The source comparison to the original affine chart. -/
def groundBaseSourceMap : (Over.map a).obj (groundBaseSource f a hL d V W t k) ⟶ A :=
  Over.homMk (pullback.fst k.left (P).left) (by
    change pullback.fst k.left (P).left ≫ A.hom =
      (pullback.snd k.left (P).left ≫ (variableHilbertTest q d W).hom) ≫ a
    rw [← Over.w k, ← Category.assoc, pullback.condition, Category.assoc, Over.w P]
    rfl)

/-- The constructed source satisfies the required original parameter equation. -/
@[reassoc]
theorem groundBaseSource_square : groundBaseSourceMap f a hL d V W t k ≫ k =
    (Over.map a).map (groundBaseSourceChart f a hL d V W t k) ≫ P :=
  Over.OverMorphism.ext (pullback.condition)

/-- The chart square is Cartesian as schemes. -/
theorem groundBaseSource_chartIsPullback :
    IsPullback (groundBaseSourceMap f a hL d V W t k).left
      (groundBaseSourceChart f a hL d V W t k).left k.left (P).left :=
  IsPullback.of_hasPullback k.left (P).left

/-- The source also is exactly the pullback of the original translation map. -/
theorem groundBaseSource_isPullback :
    IsPullback (groundBaseSourceMap f a hL d V W t k).left
      ((groundBaseSourceChart f a hL d V W t k ≫ variableHilbertBase q d W).left)
      (k ≫ variableHilbertBase f d V).left t.left :=
  (groundBaseSource_chartIsPullback f a hL d V W t k).paste_vert
    (variableHilbertGroundBase_isPullback f a hL d V W t)

/-- An original open Hilbert chart stays open on the genuinely changed family. -/
instance groundBaseSourceChart_isOpenImmersion [IsOpenImmersion k.left] :
    IsOpenImmersion (groundBaseSourceChart f a hL d V W t k).left :=
  MorphismProperty.of_isPullback (groundBaseSource_chartIsPullback f a hL d V W t k)
    (inferInstanceAs (IsOpenImmersion k.left))

/-- Affine source and translations construct an affine source over the new coefficients. -/
instance groundBaseSource_isAffine [IsAffine A.left] [IsAffine V.left] [IsAffine W.left] :
    IsAffine (groundBaseSource f a hL d V W t k).left :=
  IsAffine.of_isPullback (groundBaseSource_isPullback f a hL d V W t k)

/-- Etale translation refinements give etale source comparisons. -/
instance groundBaseSourceMap_etale [Etale t.left] :
    Etale (groundBaseSourceMap f a hL d V W t k).left :=
  MorphismProperty.of_isPullback (groundBaseSource_isPullback f a hL d V W t k).flip
    (inferInstanceAs (Etale t.left))

/-- Original source and new translation maps lift with their full scheme structures. -/
def groundBaseSourceLift {T : Over (Spec (.of R'))}
    (x : (Over.map a).obj T ⟶ A) (y : T ⟶ W)
    (hxy : x ≫ k ≫ variableHilbertBase f d V = (Over.map a).map y ≫ t) :
    T ⟶ groundBaseSource f a hL d V W t k :=
  Over.homMk ((groundBaseSource_isPullback f a hL d V W t k).lift x.left y.left
    (congrArg Over.Hom.left hxy)) (by
      rw [← Over.w (groundBaseSourceChart f a hL d V W t k ≫ variableHilbertBase q d W)]
      rw [← Category.assoc, (groundBaseSource_isPullback f a hL d V W t k).lift_snd]
      exact Over.w y)

@[reassoc]
theorem groundBaseSourceLift_source {T : Over (Spec (.of R'))}
    (x : (Over.map a).obj T ⟶ A) (y : T ⟶ W)
    (hxy : x ≫ k ≫ variableHilbertBase f d V = (Over.map a).map y ≫ t) :
    (Over.map a).map (groundBaseSourceLift f a hL d V W t k x y hxy) ≫
      groundBaseSourceMap f a hL d V W t k = x :=
  Over.OverMorphism.ext ((groundBaseSource_isPullback f a hL d V W t k).lift_fst _ _ _)

@[reassoc]
theorem groundBaseSourceLift_base {T : Over (Spec (.of R'))}
    (x : (Over.map a).obj T ⟶ A) (y : T ⟶ W)
    (hxy : x ≫ k ≫ variableHilbertBase f d V = (Over.map a).map y ≫ t) :
    groundBaseSourceLift f a hL d V W t k x y hxy ≫
      groundBaseSourceChart f a hL d V W t k ≫ variableHilbertBase q d W = y :=
  Over.OverMorphism.ext ((groundBaseSource_isPullback f a hL d V W t k).lift_snd _ _ _)

variable (c : (relativeFppfSheaf f).obj.obj (op V))

/-- The transported chart carries the original Picard section on every scheme-valued test. -/
theorem groundBaseSource_picard {T : Over (Spec (.of R'))}
    (x : T ⟶ groundBaseSource f a hL d V W t k) :
    (relativeFppfBaseChange f a).hom.hom.app (op T)
      ((relativeFppfSheaf f).obj.map
        ((Over.map a).map x ≫ groundBaseSourceMap f a hL d V W t k).op
        (sectionAt f hL d V c k)) =
    (relativeFppfSheaf q).obj.map x.op
      (sectionAt q (fixedBaseAmple f a hL) d W
        (fixedBaseTranslationClass f a V W t c) (groundBaseSourceChart f a hL d V W t k)) := by
  simp only [sectionAt, variableChartSection_map, ← variableHilbertPoint_natural,
    Category.assoc, groundBaseSource_square, ← Functor.map_comp_assoc]
  exact variableHilbertFixedBaseProjection_picard f a hL d V W t c T _

end FLT.Mazur.HilbertChart.AffineRestriction
