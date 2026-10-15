/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.GroundChartOriginalFullRelation

/-!
# The ground diagonal cuts out precisely the changed-family relation

The full original relation has two independent maps to the new ground.
Pulling back its ground-pair map along the ground diagonal recovers exactly
the changed-family relation, on all scheme tests. For an etale ground change
this is an open subrelation, with no assertion that it is the entire relation.
-/

@[expose] public noncomputable section
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry Opposite
namespace FLT.Mazur.HilbertChart.AffineRestriction
open FCurve CartierAbel SchemePicard
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
attribute [local irreducible] relation fst snd
variable {R S : Type} [CommRing R] [CommRing S]
  [Algebra.FiniteType ℤ R] [Algebra.FiniteType ℤ S]
  {X : Scheme} (f : X ⟶ Spec (.of R)) (a : Spec (.of S) ⟶ Spec (.of R))
  [IsProper f] [Flat f] [GeometricallyIntegral f] [SmoothOfRelativeDimension 1 f]
  {L : X.Modules} (hL : AmpleLineBundle L) (d : ℕ)
  (V : Over (Spec (.of R))) (W : Over (Spec (.of S)))
  (t : (Over.map a).obj W ⟶ V) (c : (relativeFppfSheaf f).obj.obj (op V))
local notation "q" => pullback.snd f a
local instance groundDiagonalRelationSmooth : SmoothOfRelativeDimension 1 q :=
  MorphismProperty.pullback_snd _ _ inferInstance
local notation "h" => fixedBaseAmple f a hL
local notation "c'" => fixedBaseTranslationClass f a V W t c
variable {B : Over (Spec (.of S))} (l : B ⟶ variableHilbertTest (pullback.snd f a) d W)


local notation "k" => groundOriginalChart f a hL d V W t l
local notation "D" => relation f hL d V c k
local notation "D'" => relation q h d W c' l
local notation "p" => fst f hL d V c k
local notation "s" => snd f hL d V c k
local notation "p'" => fst q h d W c' l
local notation "s'" => snd q h d W c' l
local notation "r" => groundRelationInclusion f a hL d V W t c l

/-- The full original relation retains both new-ground morphisms as a scheme pair. -/
def groundRelationPair : (D).left ⟶ pullback a a :=
  pullback.lift ((p).left ≫ B.hom) ((s).left ≫ B.hom) (by
    change (p).left ≫ B.hom ≫ a = (s).left ≫ B.hom ≫ a
    exact (p).w.trans (s).w.symm)

local notation "b" => groundRelationPair f a hL d V W t c l

@[reassoc]
theorem groundRelationPair_fst : b ≫ pullback.fst a a = (p).left ≫ B.hom :=
  pullback.lift_fst _ _ _

@[reassoc]
theorem groundRelationPair_snd : b ≫ pullback.snd a a = (s).left ≫ B.hom :=
  pullback.lift_snd _ _ _

/-- The changed-family relation lies over the ground diagonal as whole schemes. -/
theorem groundRelationInclusion_diagonal :
    (r).left ≫ b = (D').hom ≫ pullback.diagonal a := by
  apply pullback.hom_ext
  · simp only [Category.assoc]
    rw [groundRelationPair_fst, pullback.diagonal_fst,
      Category.comp_id, ← Category.assoc, ← Over.comp_left, groundRelationInclusion_fst]
    exact (p').w
  · simp only [Category.assoc]
    rw [groundRelationPair_snd, pullback.diagonal_snd,
      Category.comp_id, ← Category.assoc, ← Over.comp_left, groundRelationInclusion_snd]
    exact (s').w

/-- Equality of the new-ground maps is the only extra condition in the changed relation. -/
theorem groundRelationInclusion_isPullback :
    IsPullback (r).left (D').hom b (pullback.diagonal a) := by
  let lift (z : PullbackCone b (pullback.diagonal a)) := by
    have hx : z.fst ≫ (p).left ≫ B.hom = z.snd := by
      simpa only [Category.assoc, groundRelationPair_fst, pullback.diagonal_fst,
        Category.comp_id] using congrArg (fun v ↦ v ≫ pullback.fst a a) z.condition
    have hy : z.fst ≫ (s).left ≫ B.hom = z.snd := by
      simpa only [Category.assoc, groundRelationPair_snd, pullback.diagonal_snd,
        Category.comp_id] using congrArg (fun v ↦ v ≫ pullback.snd a a) z.condition
    exact groundRelationInclusion_lift f a hL d V W t c l z.fst (hx.trans hy.symm)
  refine IsPullback.of_isLimit (PullbackCone.IsLimit.mk
    (groundRelationInclusion_diagonal f a hL d V W t c l)
    (fun z ↦ (lift z).choose) (fun z ↦ (lift z).choose_spec.1.2.2) ?_ ?_)
  · intro z
    have hx : z.fst ≫ (p).left ≫ B.hom = z.snd := by
      simpa only [Category.assoc, groundRelationPair_fst, pullback.diagonal_fst,
        Category.comp_id] using congrArg (fun v ↦ v ≫ pullback.fst a a) z.condition
    rw [← (p').w, ← Category.assoc, (lift z).choose_spec.1.1, Category.assoc, hx]
  · intro z v hv _
    apply (lift z).choose_spec.2 v
    have hp := congrArg Over.Hom.left (groundRelationInclusion_fst f a hL d V W t c l)
    have hs := congrArg Over.Hom.left (groundRelationInclusion_snd f a hL d V W t c l)
    simp only [Over.comp_left, Over.map_map_left] at hp hs
    exact ⟨by rw [← hp, ← Category.assoc, hv],
      by rw [← hs, ← Category.assoc, hv], hv⟩

/-- An etale ground change cuts out an open subrelation of the full original relation. -/
instance groundRelationInclusion_isOpenImmersion [Etale a] : IsOpenImmersion (r).left :=
  MorphismProperty.of_isPullback (groundRelationInclusion_isPullback f a hL d V W t c l).flip
    (inferInstanceAs (IsOpenImmersion (pullback.diagonal a)))

end FLT.Mazur.HilbertChart.AffineRestriction
