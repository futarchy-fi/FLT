/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.OrderedHilbertFaithfulRestrictedQuotient
public import FLT.Mazur.AffineHilbertFixedBaseEnvelope

/-!
# The original tensor envelope on actual faithful tests

The local independent translation coordinate gives an open restriction of
translation. The full original relation is its pullback on the actual
local tensor envelope, without any assumption of envelope effectiveness.
-/

@[expose] public noncomputable section
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry Opposite
namespace FLT.Mazur.OrderedHilbertFaithfulTestCover
open HilbertChart CartierAbel SchemePicard FCurve AffineEtaleFaithfulNeighborhood
open OrderedHilbertAffineEtaleTestCover RelativeRelationOrbit
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
variable {R : Type} [CommRing R] [Algebra.FiniteType ℤ R] {X : Scheme}
  (f : X ⟶ Spec (.of R)) [IsProper f] [Flat f] [GeometricallyIntegral f]
  [SmoothOfRelativeDimension 1 f] {L : X.Modules} (hL : AmpleLineBundle L)
  (T : Over (Spec (.of R))) (s : (relativeFppfSheaf f).obj.obj (op T))
local notation "E" => fun x ↦ Sigma.fst (Sigma.snd (chartData f hL T s x))
local notation "b" => fun x ↦ spectrumBase
  (Over.hom (Sigma.fst (Sigma.snd (chartData f hL T s x))))
    (Sigma.fst (data f hL T s x))
local notation "q" => fun x ↦ FaithfulNeighborhoodCurve.map f
  (Over.hom (Sigma.fst (Sigma.snd (chartData f hL T s x))))
    (Sigma.fst (data f hL T s x))
local notation "degree" => fun x ↦ Prod.snd (Sigma.fst (chartData f hL T s x))

local notation "h" => fun x ↦ fixedBaseAmple f (b x) hL
local notation "c" => fun x ↦ chartClass f hL T s x
local notation "c'" => fun x ↦ localTranslationClass f hL T s x
local notation "k" => fun x ↦ toOriginalChart f hL T s x
local notation "l" => fun x ↦ localChartParameter f hL T s x
local notation "V" => fun x ↦ localTranslation f hL T s x
local notation "e" => fun x ↦ AffineRestriction.equivalence f hL (degree x) (E x) (c x) (k x)
local notation "e'" => fun x ↦
  AffineRestriction.equivalence (q x) (h x) (degree x) (V x) (c' x) (l x)

/-- The retained independent translation embeds by its actual principal open. -/
instance translationToOriginal_left_isOpenImmersion (x : T.left) :
    IsOpenImmersion (translationToOriginal f hL T s x).left := by
  change IsOpenImmersion (sourceOpen (E x).hom (data f hL T s x).1).ι
  infer_instance

instance translationToOriginal_mono (x : T.left) :
    Mono (translationToOriginal f hL T s x) := by
  apply Over.mono_of_mono_left

/-- The actual independent translation and unchanged source define the envelope map. -/
def localEnvelopeMap (x : T.left) :
    (Over.map (b x)).obj (prod (localTest f hL T s x) (V x)) ⟶
      prod (test f hL T s x) (E x) :=
  AffineRestriction.fixedBaseEnvelopeMap (b x) (E x) (V x)
    (translationToOriginal f hL T s x) (originalTestIso f hL T s x).hom

/-- The retained envelope embeds in the original envelope. -/
instance localEnvelopeMap_left_mono (x : T.left) :
    Mono (localEnvelopeMap f hL T s x).left :=
  AffineRestriction.fixedBaseEnvelopeMap_left_mono _ _ _ _ _

/-- The actual original relation is the pullback over the local independent translation. -/
theorem localEnvelope_isPullback (x : T.left) :
    IsPullback (localRestrictedRelationProjection f hL T s x).left
      (AffineRestriction.toEnvelope (q x) (h x) (degree x) (V x) (c' x) (l x)).left
      (AffineRestriction.toEnvelope f hL (degree x) (E x) (c x) (k x)).left
      (localEnvelopeMap f hL T s x).left :=
  AffineRestriction.fixedBaseEnvelope_isPullback f (b x) hL (degree x) (E x) (V x)
    (translationToOriginal f hL T s x) (c x) (k x) (l x)
    (originalTestIso f hL T s x).hom (localChartParameter_projection f hL T s x).symm

end FLT.Mazur.OrderedHilbertFaithfulTestCover
