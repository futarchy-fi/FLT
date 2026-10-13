/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.AffineHilbertGroundBaseSource
public import FLT.Mazur.AffineHilbertFixedBaseEnvelope

/-!
# Lifting the full original envelope over a changed ground base

The first endpoint is constructed from the Cartesian source square. Its new
translation coordinate is independent of the second endpoint. Equality of
the original Picard classes then constructs the full new relation arrow.
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
variable {A : Over (Spec (.of R))} (k : A ⟶ variableHilbertTest f d V)
local notation "B" => groundBaseSource f a hL d V W t k
local notation "u" => groundBaseSourceMap f a hL d V W t k
local notation "l" => groundBaseSourceChart f a hL d V W t k
local notation "h'" => fixedBaseAmple f a hL
local notation "c'" => fixedBaseTranslationClass f a V W t c
local notation "p" => fst f hL d V c k
local notation "s" => snd f hL d V c k
local notation "p'" => fst q h' d W c' l
local notation "s'" => snd q h' d W c' l
local notation "j" => toEnvelope f hL d V c k
local notation "j'" => toEnvelope q h' d W c' l
local notation "v" => fixedBaseRelationMap f a hL d V W t c k l u
  (groundBaseSource_square f a hL d V W t k)
local notation "m" => fixedBaseEnvelopeMap a V W t u
variable {T : Over (Spec (.of R'))} (r : (Over.map a).obj T ⟶ relation f hL d V c k)
  (e : T ⟶ prod (groundBaseSource f a hL d V W t k) W)
  (he : r ≫ toEnvelope f hL d V c k = (Over.map a).map e ≫
    fixedBaseEnvelopeMap a V W t (groundBaseSourceMap f a hL d V W t k))

include he in
/-- The original first endpoint and independent new translation have compatible base maps. -/
theorem groundBaseEnvelopeCone_base :
    (r ≫ p) ≫ k ≫ variableHilbertBase f d V = (Over.map a).map (e ≫ prod.snd) ≫ t := by
  have H := congrArg (fun z => z ≫ prod.snd) he
  simpa only [Category.assoc, toEnvelope_base, fixedBaseEnvelopeMap_snd,
    Functor.map_comp] using H

/-- The first endpoint retains the original point and the independent new translation. -/
def groundBaseEnvelopeConeFirst : T ⟶ B :=
  groundBaseSourceLift f a hL d V W t k (r ≫ p) (e ≫ prod.snd)
    (groundBaseEnvelopeCone_base f a hL d V W t c k r e he)

@[reassoc]
theorem groundBaseEnvelopeConeFirst_source :
    (Over.map a).map (groundBaseEnvelopeConeFirst f a hL d V W t c k r e he) ≫ u =
      r ≫ p := groundBaseSourceLift_source _ _ _ _ _ _ _ _ _ _ _

@[reassoc]
theorem groundBaseEnvelopeConeFirst_base :
    groundBaseEnvelopeConeFirst f a hL d V W t c k r e he ≫ l ≫
      variableHilbertBase q d W = e ≫ prod.snd :=
  groundBaseSourceLift_base _ _ _ _ _ _ _ _ _ _ _

include he in
/-- The independent second endpoint has exactly its prescribed original source coordinate. -/
theorem groundBaseEnvelopeCone_second :
    r ≫ s = (Over.map a).map (e ≫ prod.fst) ≫ u := by
  have H := congrArg (fun z => z ≫ prod.fst) he
  simpa only [Category.assoc, toEnvelope_test, fixedBaseEnvelopeMap_fst,
    Functor.map_comp] using H

/-- Equality of original classes constructs the local full-relation arrow. -/
def groundBaseEnvelopeConeLift : T ⟶ relation q h' d W c' l :=
  arrow q h' d W c' l (groundBaseEnvelopeConeFirst f a hL d V W t c k r e he)
    (e ≫ prod.fst)
    ((fixedBase_section_eq_iff f a hL d V W t c k l u
      (groundBaseSource_square f a hL d V W t k) _ _).mp (by
        rw [groundBaseEnvelopeConeFirst_source, ← groundBaseEnvelopeCone_second
          f a hL d V W t c k r e he]
        exact equal_class_natural f hL d V c k r))

@[reassoc]
theorem groundBaseEnvelopeConeLift_fst :
    groundBaseEnvelopeConeLift f a hL d V W t c k r e he ≫ p' =
      groundBaseEnvelopeConeFirst f a hL d V W t c k r e he :=
  arrow_fst _ _ _ _ _ _ _ _ _

@[reassoc]
theorem groundBaseEnvelopeConeLift_snd :
    groundBaseEnvelopeConeLift f a hL d V W t c k r e he ≫ s' = e ≫ prod.fst :=
  arrow_snd _ _ _ _ _ _ _ _ _

/-- The full original relation arrow is retained, without a monic base-change assumption. -/
theorem groundBaseEnvelopeConeLift_original :
    (Over.map a).map (groundBaseEnvelopeConeLift f a hL d V W t c k r e he) ≫ v = r := by
  apply hom_ext f hL d V c k
  · rw [Category.assoc, fixedBaseRelationMap_fst, ← Functor.map_comp_assoc,
      groundBaseEnvelopeConeLift_fst, groundBaseEnvelopeConeFirst_source]
  · rw [Category.assoc, fixedBaseRelationMap_snd, ← Functor.map_comp_assoc,
      groundBaseEnvelopeConeLift_snd, ← groundBaseEnvelopeCone_second f a hL d V W t c k r e he]

/-- Both new independent coordinates are retained, including every residue branch. -/
theorem groundBaseEnvelopeConeLift_envelope :
    groundBaseEnvelopeConeLift f a hL d V W t c k r e he ≫ j' = e := by
  apply prod.hom_ext
  · rw [Category.assoc, toEnvelope_test, groundBaseEnvelopeConeLift_snd]
  · rw [Category.assoc, toEnvelope_base, groundBaseEnvelopeConeLift_fst_assoc,
      groundBaseEnvelopeConeFirst_base]

end FLT.Mazur.HilbertChart.AffineRestriction
