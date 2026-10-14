/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.AffineHilbertFiniteKernelModel
public import FLT.Mazur.AffineHilbertNestedRestriction
public import FLT.Mazur.SchemeRelationMonicBaseChange

/-!
# Full Picard relations after monomorphic finite-model base change

Both original endpoints become actual pullbacks, retaining every Picard arrow.
The new projection coequalizes the full original relation on every test scheme.
The target change may be a nonreduced closed immersion; no reduction is used.
-/

@[expose] public noncomputable section
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry Opposite
namespace FLT.Mazur.HilbertChart.AffineRestriction
open CartierAbel SchemePicard FCurve
set_option backward.isDefEq.respectTransparency false
variable {R : Type} [CommRing R] [Algebra.FiniteType ℤ R] {X : Scheme}
  (f : X ⟶ Spec (.of R)) [IsProper f] [Flat f] [GeometricallyIntegral f]
  [SmoothOfRelativeDimension 1 f] {L : X.Modules} (hL : AmpleLineBundle L)
  (d : ℕ) (V : Over (Spec (.of R))) [Etale V.hom]
  (c : (relativeFppfSheaf f).obj.obj (op V))
  {A : Over (Spec (.of R))} [IsAffine A.left]
  (k : A ⟶ variableHilbertTest f d V) [IsOpenImmersion k.left]
  {B : Over (Spec (.of R))} (u : B ⟶ A) {T : Scheme}
  (i : T ⟶ (finiteKernelModel f hL d V c k).left) [Mono i] (w : B.left ⟶ T)
  (h : IsPullback u.left w (finiteKernelProjection f hL d V c k).left i)
local notation "p" => fst f hL d V c k
local notation "q" => snd f hL d V c k
local notation "p'" => fst f hL d V c (u ≫ k)
local notation "q'" => snd f hL d V c (u ≫ k)
local notation "α" => nestedToFullRelation f hL d V c k u
local notation "e" => nestedSchemeDoubleIso f hL d V c k u
local notation "v" => finiteKernelProjection f hL d V c k

include h in
/-- The full double comparison preserves its first endpoint in the actual new source. -/
@[reassoc]
theorem monicModelRelationIso_fst : (e).hom ≫
    SchemeRelationRestriction.fst (p).left (q).left u.left = (p').left := by
  let _ := h.mono_fst_of_mono
  apply (cancel_mono u.left).mp
  rw [Category.assoc, ← SchemeRelationRestriction.arrow_fst,
    ← Category.assoc, nestedSchemeDoubleIso_arrow]
  exact congrArg Over.Hom.left (nestedToFullRelation_fst f hL d V c k u)

include h in
/-- The independent second endpoint is retained as well. -/
@[reassoc]
theorem monicModelRelationIso_snd : (e).hom ≫
    SchemeRelationRestriction.snd (p).left (q).left u.left = (q').left := by
  let _ := h.mono_fst_of_mono
  apply (cancel_mono u.left).mp
  rw [Category.assoc, ← SchemeRelationRestriction.arrow_snd,
    ← Category.assoc, nestedSchemeDoubleIso_arrow]
  exact congrArg Over.Hom.left (nestedToFullRelation_snd f hL d V c k u)

include h in
/-- The original Picard relation, not the candidate kernel, has this first pullback square. -/
theorem monicModelRelation_fst_isPullback :
    IsPullback (α).left (p').left (p).left u.left := by
  have he := congrArg Over.Hom.left (finiteKernelProjection_condition f hL d V c k)
  exact (SchemeRelationRestriction.monicBase_fst_isPullback
    (p).left (q).left (v).left i u.left w h he).of_iso'
      e (Iso.refl _) (Iso.refl _) (Iso.refl _)
      (by simpa using nestedSchemeDoubleIso_arrow f hL d V c k u)
      (by simpa using monicModelRelationIso_fst f hL d V c k u i w h)
      (by simp) (by simp)

include h in
/-- The same complete original relation is also the pullback of the second endpoint. -/
theorem monicModelRelation_snd_isPullback :
    IsPullback (α).left (q').left (q).left u.left := by
  have he := congrArg Over.Hom.left (finiteKernelProjection_condition f hL d V c k)
  exact (SchemeRelationRestriction.monicBase_snd_isPullback
    (p).left (q).left (v).left i u.left w h he).of_iso'
      e (Iso.refl _) (Iso.refl _) (Iso.refl _)
      (by simpa using nestedSchemeDoubleIso_arrow f hL d V c k u)
      (by simpa using monicModelRelationIso_snd f hL d V c k u i w h)
      (by simp) (by simp)

include h in
/-- The actual new projection coequalizes the full original Picard relation. -/
@[reassoc]
theorem monicModelRelation_condition : (p').left ≫ w = (q').left ≫ w := by
  apply (cancel_mono i).mp
  rw [Category.assoc, Category.assoc, ← h.w, ← Category.assoc, ← Category.assoc]
  change ((p' ≫ u) ≫ v).left = ((q' ≫ u) ≫ v).left
  rw [← nestedToFullRelation_fst, ← nestedToFullRelation_snd,
    Category.assoc, Category.assoc, finiteKernelProjection_condition]

/-- The unchanged full Picard relation embeds into the actual new projection kernel. -/
def monicModelRelationKernelMap : (relation f hL d V c (u ≫ k)).left ⟶ pullback w w :=
  pullback.lift (p').left (q').left (monicModelRelation_condition f hL d V c k u i w h)

/-- The comparison loses no arrows; its surjectivity remains a separate geometric task. -/
instance monicModelRelationKernelMap_mono :
    Mono (monicModelRelationKernelMap f hL d V c k u i w h) where
  right_cancellation := by
    intro Z a b hab
    have ha : a ≫ (p').left = b ≫ (p').left := by
      simpa only [monicModelRelationKernelMap, Category.assoc, pullback.lift_fst] using
        congrArg (fun z ↦ z ≫ pullback.fst w w) hab
    have hb : a ≫ (q').left = b ≫ (q').left := by
      simpa only [monicModelRelationKernelMap, Category.assoc, pullback.lift_snd] using
        congrArg (fun z ↦ z ≫ pullback.snd w w) hab
    let Z' := Over.mk (a ≫ (relation f hL d V c (u ≫ k)).hom)
    let a' : Z' ⟶ relation f hL d V c (u ≫ k) := Over.homMk a
    let b' : Z' ⟶ relation f hL d V c (u ≫ k) := Over.homMk b (by
      change b ≫ (relation f hL d V c (u ≫ k)).hom =
        a ≫ (relation f hL d V c (u ≫ k)).hom
      rw [← (p').w, ← Category.assoc, ← Category.assoc, ha])
    exact congrArg Over.Hom.left (hom_ext f hL d V c (u ≫ k)
      (a := a') (b := b') (Over.OverMorphism.ext ha) (Over.OverMorphism.ext hb))

end FLT.Mazur.HilbertChart.AffineRestriction
