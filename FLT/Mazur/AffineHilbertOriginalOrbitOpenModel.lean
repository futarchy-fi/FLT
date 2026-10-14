/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.AffineHilbertOriginalOrbitModel
public import FLT.Mazur.SchemeRelationOrbitOpenModel

/-!
# Genuine original Hilbert open selections from effective orbit atlases

The orbit atlas descends to its actual open image in the original parameter
scheme. The rebuilt original-family Picard relation is its entire quotient
kernel. This constructs open selections without pretending the atlas is open.
-/

@[expose] public noncomputable section
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry Opposite
namespace FLT.Mazur.HilbertChart.AffineRestriction
open CartierAbel SchemePicard FCurve
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
attribute [local irreducible] relation fst snd
variable {R : Type} [CommRing R] [Algebra.FiniteType ℤ R] {X : Scheme}
  (f : X ⟶ Spec (.of R)) [IsProper f] [Flat f] [GeometricallyIntegral f]
  [SmoothOfRelativeDimension 1 f] {L : X.Modules} (hL : AmpleLineBundle L)
  (d : ℕ) (V : Over (Spec (.of R))) [Etale V.hom]
  (c : (relativeFppfSheaf f).obj.obj (op V))
  {A : Over (Spec (.of R))} (k : A ⟶ variableHilbertTest f d V)
  [IsOpenImmersion k.left] {Z : Scheme} (s : Z ⟶ A.left) [Etale s]
local notation "p" => fst f hL d V c k
local notation "q" => snd f hL d V c k
local notation "e" => equivalence f hL d V c k
local notation "U" => SchemeRelationOrbitOpenModel.sourceOpen («p» := p) («q» := q) s

/-- An actual open original-family parameter source over the unchanged original ground. -/
def originalOrbitOpenSource : Over (Spec (.of R)) := Over.mk ((U).ι ≫ A.hom)

/-- This map, unlike the orbit atlas itself, is a genuine open immersion. -/
def originalOrbitOpenToSource : originalOrbitOpenSource f hL d V c k s ⟶ A :=
  Over.homMk (U).ι

/-- A genuine open Hilbert reselection for the ORIGINAL proper family. -/
def originalOrbitOpenParameter : originalOrbitOpenSource f hL d V c k s ⟶
    variableHilbertTest f d V := originalOrbitOpenToSource f hL d V c k s ≫ k

local notation "u" => originalOrbitOpenToSource f hL d V c k s
local notation "l" => originalOrbitOpenParameter f hL d V c k s
local notation "p'" => fst f hL d V c l
local notation "q'" => snd f hL d V c l

instance originalOrbitOpenToSource_isOpenImmersion : IsOpenImmersion (u).left :=
  inferInstanceAs (IsOpenImmersion (U).ι)

instance originalOrbitOpenParameter_isOpenImmersion : IsOpenImmersion (l).left :=
  inferInstanceAs (IsOpenImmersion ((u).left ≫ k.left))

/-- Every seed point is retained in the genuine original open selection. -/
theorem originalOrbitOpen_seed_point (z : Z) :
    ∃ x : (originalOrbitOpenSource f hL d V c k s).left,
      (u).left x = s z ∧ (l).left x = k.left (s z) :=
  ⟨⟨s z, SchemeRelationOrbitOpenModel.seed_mem e s z⟩, rfl, rfl⟩

/-- The first endpoint of the rebuilt full original relation is unchanged. -/
@[reassoc]
theorem originalOrbitOpenDoubleIso_fst : (nestedSchemeDoubleIso f hL d V c k u).hom ≫
    SchemeRelationRestriction.fst (p).left (q).left (u).left = (p').left := by
  dsimp only [nestedSchemeDoubleIso, Iso.trans_hom, Functor.mapIso_hom,
    SchemeRelationRestriction.overDoubleIso]
  rw [Category.assoc, SchemeRelationRestriction.overToDouble_fst]
  exact congrArg Over.Hom.left (nestedToFullDouble_fst f hL d V c k u)

/-- The independent second endpoint is unchanged as a scheme morphism. -/
@[reassoc]
theorem originalOrbitOpenDoubleIso_snd : (nestedSchemeDoubleIso f hL d V c k u).hom ≫
    SchemeRelationRestriction.snd (p).left (q).left (u).left = (q').left := by
  dsimp only [nestedSchemeDoubleIso, Iso.trans_hom, Functor.mapIso_hom,
    SchemeRelationRestriction.overDoubleIso]
  rw [Category.assoc, SchemeRelationRestriction.overToDouble_snd]
  exact congrArg Over.Hom.left (nestedToFullDouble_snd f hL d V c k u)

attribute [local irreducible] SchemeRelationRestriction.doubleDomain
  SchemeRelationRestriction.fst SchemeRelationRestriction.snd
variable {Q : Scheme} (w : Z ⟶ Q)

/-- The descended model of the actual original-family open selection. -/
def originalOrbitOpenModel
    (H : IsPullback (SchemeRelationRestriction.fst (p).left (q).left s)
      (SchemeRelationRestriction.snd (p).left (q).left s) w w) :
    (originalOrbitOpenSource f hL d V c k s).left ⟶ Q :=
  SchemeRelationOrbitOpenModel.projection e s w H

/-- The rebuilt original Picard relation is the FULL scheme kernel of this open-source model. -/
theorem originalOrbitOpenModel_isPullback
    (H : IsPullback (SchemeRelationRestriction.fst (p).left (q).left s)
    (SchemeRelationRestriction.snd (p).left (q).left s) w w) : IsPullback (p').left (q').left
    (originalOrbitOpenModel f hL d V c k s w H)
    (originalOrbitOpenModel f hL d V c k s w H) := by
  apply (SchemeRelationOrbitOpenModel.isPullback e s w H).of_iso'
    (nestedSchemeDoubleIso f hL d V c k u) (Iso.refl _) (Iso.refl _) (Iso.refl _)
  · change (nestedSchemeDoubleIso f hL d V c k u).hom ≫
      SchemeRelationRestriction.fst (p).left (q).left (u).left = (p').left ≫ 𝟙 _
    simpa only [Category.comp_id] using originalOrbitOpenDoubleIso_fst f hL d V c k s
  · change (nestedSchemeDoubleIso f hL d V c k u).hom ≫
      SchemeRelationRestriction.snd (p).left (q).left (u).left = (q').left ≫ 𝟙 _
    simpa only [Category.comp_id] using originalOrbitOpenDoubleIso_snd f hL d V c k s
  · simp only [Iso.refl_hom, Category.id_comp, Category.comp_id]
    rfl
  · simp only [Iso.refl_hom, Category.id_comp, Category.comp_id]
    rfl

/-- The constructed original open-source model is an actual etale cover. -/
theorem originalOrbitOpenModel_cover
    (H : IsPullback (SchemeRelationRestriction.fst (p).left (q).left s)
    (SchemeRelationRestriction.snd (p).left (q).left s) w w) [Etale w] [Surjective w] :
    Etale (originalOrbitOpenModel f hL d V c k s w H) ∧
      Surjective (originalOrbitOpenModel f hL d V c k s w H) :=
  SchemeRelationOrbitOpenModel.cover e s w H

/-- The entire quotient morphism retains the original proper-family ground. -/
@[reassoc]
theorem originalOrbitOpenModel_ground
    (H : IsPullback (SchemeRelationRestriction.fst (p).left (q).left s)
    (SchemeRelationRestriction.snd (p).left (q).left s) w w) (a : Q ⟶ Spec (.of R))
    (ha : w ≫ a = s ≫ A.hom) : originalOrbitOpenModel f hL d V c k s w H ≫ a =
      (originalOrbitOpenSource f hL d V c k s).hom :=
  SchemeRelationOrbitOpenModel.projection_ground e s w H a ha

end FLT.Mazur.HilbertChart.AffineRestriction
