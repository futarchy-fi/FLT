/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.AffineHilbertFixedBaseRelationInverse

/-!
# The original tensor envelope under coefficient localization

The two independent envelope coordinates give an actual comparison. When
translation restriction is monic, the original full relation is exactly the
pullback of its original envelope inclusion to this local envelope.
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

/-- The actual envelope comparison retains the source and independent translation coordinates. -/
def fixedBaseEnvelopeMap : (Over.map a).obj (prod B W) ⟶ prod A V :=
  prod.lift ((Over.map a).map prod.fst ≫ u) ((Over.map a).map prod.snd ≫ t)

omit [Algebra.FiniteType ℤ R] [Algebra.FiniteType ℤ R'] [Mono a] [IsIso u] in
/-- The original test coordinate of the envelope comparison. -/
@[reassoc]
theorem fixedBaseEnvelopeMap_fst :
    fixedBaseEnvelopeMap a V W t u ≫ prod.fst = (Over.map a).map prod.fst ≫ u :=
  prod.lift_fst _ _

omit [Algebra.FiniteType ℤ R] [Algebra.FiniteType ℤ R'] [Mono a] [IsIso u] in
/-- The independent original translation coordinate of the envelope comparison. -/
@[reassoc]
theorem fixedBaseEnvelopeMap_snd :
    fixedBaseEnvelopeMap a V W t u ≫ prod.snd = (Over.map a).map prod.snd ≫ t :=
  prod.lift_snd _ _

omit [Mono a] [IsIso u] in
/-- The full original relation comparison commutes with the actual envelope inclusions. -/
theorem fixedBaseEnvelope_square :
    fixedBaseRelationMap f a hL d V W t c k l u hu ≫ toEnvelope f hL d V c k =
      (Over.map a).map (toEnvelope q h d W c' l) ≫ fixedBaseEnvelopeMap a V W t u := by
  apply prod.hom_ext
  · rw [Category.assoc, toEnvelope_test, fixedBaseRelationMap_snd,
      Category.assoc, fixedBaseEnvelopeMap_fst, ← Functor.map_comp_assoc, toEnvelope_test]
  · have hh : u ≫ k ≫ variableHilbertBase f d V =
        (Over.map a).map l ≫ (Over.map a).map (variableHilbertBase q d W) ≫ t := by
      rw [← Category.assoc, hu, Category.assoc, variableHilbertFixedBaseProjection_base]
    rw [Category.assoc, toEnvelope_base, fixedBaseRelationMap_fst_assoc,
      Category.assoc, hh, fixedBaseEnvelopeMap_snd]
    simp only [← Functor.map_comp_assoc, toEnvelope_base]

/-- A monic translation restriction embeds the local envelope in the original envelope. -/
instance fixedBaseEnvelopeMap_left_mono [Mono t] :
    Mono (fixedBaseEnvelopeMap a V W t u).left := by
  constructor
  intro Z g j he
  apply (cancel_mono (Over.prodLeftIsoPullback B W).hom).mp
  apply pullback.hom_ext
  · rw [Category.assoc, Category.assoc, Over.prodLeftIsoPullback_hom_fst]
    apply (cancel_mono u.left).mp
    have h₁ := congrArg (fun z ↦ z ≫ (prod.fst : prod A V ⟶ A).left) he
    have h₂ := congrArg Over.Hom.left (fixedBaseEnvelopeMap_fst a V W t u)
    simp only [Over.comp_left, Over.map_map_left] at h₂
    simpa only [Category.assoc, h₂] using h₁
  · rw [Category.assoc, Category.assoc, Over.prodLeftIsoPullback_hom_snd]
    apply (cancel_mono t.left).mp
    have h₁ := congrArg (fun z ↦ z ≫ (prod.snd : prod A V ⟶ V).left) he
    have h₂ := congrArg Over.Hom.left (fixedBaseEnvelopeMap_snd a V W t u)
    simp only [Over.comp_left, Over.map_map_left] at h₂
    simpa only [Category.assoc, h₂] using h₁

/-- The localized envelope cuts out the entire original relation by an actual scheme pullback. -/
theorem fixedBaseEnvelope_isPullback [Mono t] :
    IsPullback (fixedBaseRelationMap f a hL d V W t c k l u hu).left
      (toEnvelope q h d W c' l).left (toEnvelope f hL d V c k).left
      (fixedBaseEnvelopeMap a V W t u).left := by
  let _ : IsIso (fixedBaseRelationMap f a hL d V W t c k l u hu).left :=
    inferInstanceAs (IsIso ((Over.forget _).mapIso
      (fixedBaseRelationIso f a hL d V W t c k l u hu)).hom)
  exact IsPullback.of_horiz_isIso_mono
    ⟨congrArg Over.Hom.left (fixedBaseEnvelope_square f a hL d V W t c k l u hu)⟩

end FLT.Mazur.HilbertChart.AffineRestriction
