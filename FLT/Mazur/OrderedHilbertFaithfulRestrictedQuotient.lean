/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.OrderedHilbertFaithfulChartProjection
public import FLT.Mazur.AffineHilbertFixedBaseQuotient

/-!
# Original full relations and invariant quotients on faithful affine tests

The actual original-test isomorphism supplies the restricted comparison.
Both endpoints and the invariant locally ringed projection are retained on
the same underlying affine source, with no added effectiveness hypothesis.
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

/-- The actual localized restricted full relation maps to the original restricted relation. -/
def localRestrictedRelationProjection (x : T.left) :
    (Over.map (b x)).obj
        (AffineRestriction.relation (q x) (h x) (degree x) (V x) (c' x) (l x)) ⟶
      AffineRestriction.relation f hL (degree x) (E x) (c x) (k x) :=
  AffineRestriction.fixedBaseRelationMap f (b x) hL (degree x) (E x) (V x)
    (translationToOriginal f hL T s x) (c x) (k x) (l x)
    (originalTestIso f hL T s x).hom (localChartParameter_projection f hL T s x).symm

/-- The original first endpoint is unchanged on the retained affine source. -/
theorem localRestrictedRelationProjection_fst (x : T.left) :
    (localRestrictedRelationProjection f hL T s x).left ≫
        (AffineRestriction.fst f hL (degree x) (E x) (c x) (k x)).left =
      (AffineRestriction.fst (q x) (h x) (degree x) (V x) (c' x) (l x)).left := by
  have hh := congrArg Over.Hom.left
    (AffineRestriction.fixedBaseRelationMap_fst f (b x) hL (degree x) (E x) (V x)
      (translationToOriginal f hL T s x) (c x) (k x) (l x)
      (originalTestIso f hL T s x).hom (localChartParameter_projection f hL T s x).symm)
  simpa only [localRestrictedRelationProjection, localTranslationClass,
    Over.comp_left, Over.map_map_left, originalTestIso_hom_left, Category.comp_id] using hh

/-- The independently varying second endpoint is also unchanged. -/
theorem localRestrictedRelationProjection_snd (x : T.left) :
    (localRestrictedRelationProjection f hL T s x).left ≫
        (AffineRestriction.snd f hL (degree x) (E x) (c x) (k x)).left =
      (AffineRestriction.snd (q x) (h x) (degree x) (V x) (c' x) (l x)).left := by
  have hh := congrArg Over.Hom.left
    (AffineRestriction.fixedBaseRelationMap_snd f (b x) hL (degree x) (E x) (V x)
      (translationToOriginal f hL T s x) (c x) (k x) (l x)
      (originalTestIso f hL T s x).hom (localChartParameter_projection f hL T s x).symm)
  simpa only [localRestrictedRelationProjection, localTranslationClass,
    Over.comp_left, Over.map_map_left, originalTestIso_hom_left, Category.comp_id] using hh

/-- The original invariant locally ringed quotients on the actual affine tests are compared. -/
def localRestrictedQuotientMap (x : T.left) :
    invariantLocallyRingedSpace (e' x) ⟶ invariantLocallyRingedSpace (e x) :=
  AffineRestriction.fixedBaseQuotientMap f (b x) hL (degree x) (E x) (V x)
    (translationToOriginal f hL T s x) (c x) (k x) (l x)
    (originalTestIso f hL T s x).hom (localChartParameter_projection f hL T s x).symm

/-- The local comparison retains literally the original affine source projection. -/
@[reassoc]
theorem localRestrictedQuotientMap_projection (x : T.left) :
    invariantLocallyRingedProjection (e' x) ≫ localRestrictedQuotientMap f hL T s x =
      invariantLocallyRingedProjection (e x) := by
  have hh := AffineRestriction.fixedBaseQuotientMap_projection f (b x) hL (degree x)
    (E x) (V x) (translationToOriginal f hL T s x) (c x) (k x) (l x)
    (originalTestIso f hL T s x).hom (localChartParameter_projection f hL T s x).symm
  change invariantLocallyRingedProjection (e' x) ≫
    localRestrictedQuotientMap f hL T s x = (𝟙 _) ≫ invariantLocallyRingedProjection (e x) at hh
  simpa only [Category.id_comp] using hh

/-- No original restricted orbit is lost by passing to the localized model. -/
theorem localRestrictedQuotientMap_surjective (x : T.left) :
    Function.Surjective (localRestrictedQuotientMap f hL T s x).base := by
  intro z
  obtain ⟨y, rfl⟩ := projection_surjective (e x) z
  refine ⟨projection (e' x) y, ?_⟩
  have hh := congrArg (fun g ↦ g.base) (localRestrictedQuotientMap_projection f hL T s x)
  rw [LocallyRingedSpace.comp_base, invariantLocallyRingedProjection_base,
    invariantLocallyRingedProjection_base] at hh
  exact congrArg (fun g ↦ g y) hh

end FLT.Mazur.OrderedHilbertFaithfulTestCover
