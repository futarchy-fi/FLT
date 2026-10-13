/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.OrderedHilbertFaithfulRestrictedQuotient
public import FLT.Mazur.AffineHilbertFixedBaseQuotientIso

/-!
# Original relation and invariant quotient isomorphisms on faithful tests

Monicity of the actual spectrum neighborhood and the original test isomorphism
make both constructed comparisons invertible. No envelope effectiveness is
assumed or concluded.
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

/-- The actual faithful test retains the FULL original restricted relation up to isomorphism. -/
def localRestrictedRelationIso (x : T.left) :
    (Over.map (b x)).obj
        (AffineRestriction.relation (q x) (h x) (degree x) (V x) (c' x) (l x)) ≅
      AffineRestriction.relation f hL (degree x) (E x) (c x) (k x) :=
  AffineRestriction.fixedBaseRelationIso f (b x) hL (degree x) (E x) (V x)
    (translationToOriginal f hL T s x) (c x) (k x) (l x)
    (originalTestIso f hL T s x).hom (localChartParameter_projection f hL T s x).symm

/-- Its forward map is the already constructed original relation projection. -/
theorem localRestrictedRelationIso_hom (x : T.left) :
    (localRestrictedRelationIso f hL T s x).hom =
      localRestrictedRelationProjection f hL T s x := rfl

/-- The faithful restricted quotient is the ORIGINAL invariant locally ringed space. -/
def localRestrictedQuotientIso (x : T.left) :
    invariantLocallyRingedSpace (e' x) ≅ invariantLocallyRingedSpace (e x) :=
  AffineRestriction.fixedBaseQuotientIso f (b x) hL (degree x) (E x) (V x)
    (translationToOriginal f hL T s x) (c x) (k x) (l x)
    (originalTestIso f hL T s x).hom (localChartParameter_projection f hL T s x).symm

/-- This is exactly the existing invariant quotient map, including its sheaf morphism. -/
theorem localRestrictedQuotientIso_hom (x : T.left) :
    (localRestrictedQuotientIso f hL T s x).hom =
      localRestrictedQuotientMap f hL T s x := rfl

instance localRestrictedQuotientMap_isIso (x : T.left) :
    IsIso (localRestrictedQuotientMap f hL T s x) := by
  rw [← localRestrictedQuotientIso_hom]
  infer_instance

/-- The inverse comparison also retains literally the original affine source projection. -/
@[reassoc]
theorem localRestrictedQuotientIso_inv_projection (x : T.left) :
    invariantLocallyRingedProjection (e x) ≫ (localRestrictedQuotientIso f hL T s x).inv =
      invariantLocallyRingedProjection (e' x) := by
  have hh := AffineRestriction.fixedBaseQuotientIso_inv_projection f (b x) hL (degree x)
    (E x) (V x) (translationToOriginal f hL T s x) (c x) (k x) (l x)
    (originalTestIso f hL T s x).hom (localChartParameter_projection f hL T s x).symm
  rw [IsIso.inv_eq_of_hom_inv_id (originalTestIso f hL T s x).hom_inv_id] at hh
  change invariantLocallyRingedProjection (e x) ≫
    (localRestrictedQuotientIso f hL T s x).inv =
      (𝟙 _) ≫ invariantLocallyRingedProjection (e' x) at hh
  simpa only [Category.id_comp] using hh

/-- The original and localized orbit spaces have the same topology, not just the same points. -/
def localRestrictedOrbitHomeomorph (x : T.left) : Orbit (e' x) ≃ₜ Orbit (e x) :=
  TopCat.homeoOfIso (LocallyRingedSpace.forgetToTop.mapIso
    (localRestrictedQuotientIso f hL T s x))

end FLT.Mazur.OrderedHilbertFaithfulTestCover
