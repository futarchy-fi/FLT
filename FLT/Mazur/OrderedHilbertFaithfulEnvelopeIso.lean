/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.OrderedHilbertFaithfulEnvelope
public import FLT.Mazur.OrderedHilbertFaithfulRestrictedIso
public import FLT.Mazur.AffineHilbertCartesianEnvelope

/-!
# The faithful tensor envelope is the entire original envelope

The translation is the full inverse image of the chosen base open. Since
the affine source is already over this open, its envelope comparison is an
isomorphism. Full-envelope effectiveness is therefore equivalent on both
models; base localization by itself does not establish it.
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

/-- The actual translation square is Cartesian, not just a monomorphism square. -/
theorem translationToOriginal_isPullback (x : T.left) :
    IsPullback (translationToOriginal f hL T s x).left (V x).hom (E x).hom (b x) :=
  spectrum_isPullback (E x).hom (data f hL T s x).1

/-- The faithful-base change retains the entire independent-coordinate envelope. -/
instance localEnvelopeMap_isIso (x : T.left) : IsIso (localEnvelopeMap f hL T s x).left :=
  AffineRestriction.fixedBaseEnvelopeMap_isIso (b x) (E x) (V x)
    (translationToOriginal f hL T s x) (originalTestIso f hL T s x).hom
    (translationToOriginal_isPullback f hL T s x)

/-- An actual scheme isomorphism of the two full tensor envelopes. -/
def localEnvelopeIso (x : T.left) :
    (prod (localTest f hL T s x) (V x)).left ≅
      (prod (test f hL T s x) (E x)).left :=
  asIso (localEnvelopeMap f hL T s x).left

/-- The full original relation comparison is invertible on underlying schemes. -/
instance localRestrictedRelationProjection_left_isIso (x : T.left) :
    IsIso (localRestrictedRelationProjection f hL T s x).left :=
  inferInstanceAs (IsIso ((Over.forget _).mapIso
    (localRestrictedRelationIso f hL T s x)).hom)

/-- Filling the original envelope is exactly the same problem after faithful base localization. -/
theorem localEnvelope_full_iff (x : T.left) :
    IsIso (AffineRestriction.toEnvelope f hL (degree x) (E x) (c x) (k x)).left ↔
      IsIso (AffineRestriction.toEnvelope (q x) (h x) (degree x) (V x) (c' x) (l x)).left := by
  have hs := (localEnvelope_isPullback f hL T s x).w
  constructor
  · intro hi
    rw [← isIso_comp_right_iff _ (localEnvelopeMap f hL T s x).left, ← hs]
    infer_instance
  · intro hi
    rw [← isIso_comp_left_iff (localRestrictedRelationProjection f hL T s x).left, hs]
    infer_instance

end FLT.Mazur.OrderedHilbertFaithfulTestCover
