/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.AffineHilbertTranslationOriginalEnvelope

/-!
# Cartesian original envelopes for constructed translation sources

The original relation arrow and the new independent coordinates uniquely
lift to the refined full relation. Translation changes need not be monic.
-/

@[expose] public noncomputable section
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry Opposite
namespace FLT.Mazur.HilbertChart.AffineRestriction
open CartierAbel SchemePicard FCurve
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
variable {R : Type} [CommRing R] [Algebra.FiniteType ℤ R] {X : Scheme}
  (f : X ⟶ Spec (.of R)) [IsProper f] [Flat f] [GeometricallyIntegral f]
  [SmoothOfRelativeDimension 1 f] {L : X.Modules} (hL : AmpleLineBundle L)
  (d : ℕ) {V W : Over (Spec (.of R))} (b : W ⟶ V)
  (c : (relativeFppfSheaf f).obj.obj (op V))
  {A : Over (Spec (.of R))} (k : A ⟶ variableHilbertTest f d V)
local notation "u" => translationSourceMap f d b k
local notation "l" => translationSourceChart f d b k
local notation "c'" => CategoryTheory.Functor.map
  (ObjectProperty.FullSubcategory.obj (relativeFppfSheaf f)) (Quiver.Hom.op b) c

local notation "p" => fst f hL d V c k
local notation "q" => snd f hL d V c k
local notation "p'" => fst f hL d W c' l
local notation "q'" => snd f hL d W c' l
local notation "j" => toEnvelope f hL d V c k
local notation "j'" => toEnvelope f hL d W c' l
local notation "v" => translationSourceRelationMap f hL d b c k

variable {T : Over (Spec (.of R))} (r : T ⟶ relation f hL d V c k)
  (e : T ⟶ prod (translationSource f d b k) W)
  (h : r ≫ toEnvelope f hL d V c k =
    e ≫ prod.map (translationSourceMap f d b k) b)

/-- The lifted cone endpoints have equal original Picard classes. -/
theorem translationEnvelopeCone_class :
    (relativeFppfSheaf f).obj.map
        (translationEnvelopeConeFirst f hL d b c k r e h ≫ u).op
        (sectionAt f hL d V c k) =
      (relativeFppfSheaf f).obj.map ((e ≫ prod.fst) ≫ u).op
        (sectionAt f hL d V c k) := by
  rw [translationEnvelopeConeFirst_source, ← translationEnvelopeCone_second f hL d b c k r e h]
  exact equal_class_natural f hL d V c k r

/-- The refined relation arrow is constructed using equality of the original classes. -/
def translationEnvelopeConeLift : T ⟶ relation f hL d W c' l :=
  arrow f hL d W c' l (translationEnvelopeConeFirst f hL d b c k r e h) (e ≫ prod.fst)
    ((translationSource_equal_class_iff f hL d b c k _ _).mp
      (translationEnvelopeCone_class f hL d b c k r e h))

@[reassoc]
theorem translationEnvelopeConeLift_fst :
    translationEnvelopeConeLift f hL d b c k r e h ≫ p' =
      translationEnvelopeConeFirst f hL d b c k r e h := arrow_fst f hL d W c' l _ _ _

@[reassoc]
theorem translationEnvelopeConeLift_snd :
    translationEnvelopeConeLift f hL d b c k r e h ≫ q' = e ≫ prod.fst :=
  arrow_snd f hL d W c' l _ _ _

/-- The constructed lift retains the given original full relation arrow. -/
theorem translationEnvelopeConeLift_original :
    translationEnvelopeConeLift f hL d b c k r e h ≫ v = r := by
  apply hom_ext f hL d V c k
  · rw [Category.assoc, translationSourceRelationMap_fst,
      translationEnvelopeConeLift_fst_assoc, translationEnvelopeConeFirst_source]
  · rw [Category.assoc, translationSourceRelationMap_snd,
      translationEnvelopeConeLift_snd_assoc, ← Category.assoc,
      ← translationEnvelopeCone_second f hL d b c k r e h]

/-- The constructed lift retains both independent refined envelope coordinates. -/
theorem translationEnvelopeConeLift_envelope :
    translationEnvelopeConeLift f hL d b c k r e h ≫ j' = e := by
  apply prod.hom_ext
  · rw [Category.assoc, toEnvelope_test, translationEnvelopeConeLift_snd]
  · rw [Category.assoc, toEnvelope_base, translationEnvelopeConeLift_fst_assoc,
      translationEnvelopeConeFirst_base]

/-- The actual envelope square is Cartesian, including for nonmonic translation changes. -/
theorem translationSourceEnvelope_isPullback : IsPullback v j' j (prod.map u b) := by
  refine IsPullback.of_isLimit (PullbackCone.IsLimit.mk
    (translationSourceEnvelope_square f hL d b c k)
    (fun z => translationEnvelopeConeLift f hL d b c k z.fst z.snd z.condition)
    (fun z => translationEnvelopeConeLift_original f hL d b c k z.fst z.snd z.condition)
    (fun z => translationEnvelopeConeLift_envelope f hL d b c k z.fst z.snd z.condition)
    (fun z t ht he => ?_))
  apply hom_ext f hL d W c' l
  · rw [translationEnvelopeConeLift_fst]
    apply (translationSource_isPullback f d b k).hom_ext
    · rw [translationEnvelopeConeFirst_source, Category.assoc,
        ← translationSourceRelationMap_fst, ← Category.assoc, ht]
    · rw [translationEnvelopeConeFirst_base, Category.assoc,
        ← toEnvelope_base, ← Category.assoc, he]
  · rw [translationEnvelopeConeLift_snd, ← toEnvelope_test, ← Category.assoc, he]

/-- The same Cartesian square on schemes permits transport of actual envelope points. -/
theorem translationSourceEnvelope_schemeIsPullback :
    IsPullback (v).left (j').left (j).left (prod.map u b).left :=
  (translationSourceEnvelope_isPullback f hL d b c k).map (Over.forget _)

end FLT.Mazur.HilbertChart.AffineRestriction
