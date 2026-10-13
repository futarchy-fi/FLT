/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.AffineHilbertDerivedNoetherianRelation
public import FLT.Mazur.AffineHilbertPrincipalInvariants

/-!
# Original principal invariants without an additional Noetherian assumption

All source and relation finiteness requirements are now derived from the
original proper family and affine étale translation. The entire two-endpoint
restriction retains its geometric invariant sections and original base square.
-/

@[expose] public noncomputable section
open CategoryTheory AlgebraicGeometry Opposite
namespace FLT.Mazur.HilbertChart.AffineRestriction
open CartierAbel SchemePicard FCurve SchemeEffectiveEpiSections
open SchemeRelationInvariantSpectrum
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
variable {R : Type} [CommRing R] [Algebra.FiniteType ℤ R] {X : Scheme}
  (f : X ⟶ Spec (.of R)) [IsProper f] [Flat f] [GeometricallyIntegral f]
  [SmoothOfRelativeDimension 1 f] {L : X.Modules} (hL : AmpleLineBundle L)
  (d : ℕ) (V : Over (Spec (.of R))) [IsAffine V.left] [Etale V.hom]
  (c : (relativeFppfSheaf f).obj.obj (op V))
  {A : Over (Spec (.of R))} [IsAffine A.left]
  (k : A ⟶ variableHilbertTest f d V) [IsOpenImmersion k.left]
local notation "p" => fst f hL d V c k
local notation "q" => snd f hL d V c k
variable (s : compatibleFunctions
  (FLT.Mazur.HilbertChart.AffineRestriction.fst f hL d V c k).left
  (FLT.Mazur.HilbertChart.AffineRestriction.snd f hL d V c k).left)
local notation "W" => A.left.basicOpen s.val

/-- The actual full restricted invariant ring is the localization of the original invariant ring. -/
def originalPrincipalFullInvariantEquiv : Localization.Away s ≃+*
    compatibleFunctions (SchemeRelationRestriction.fst (p).left (q).left (W).ι)
      (SchemeRelationRestriction.snd (p).left (q).left (W).ι) :=
  SchemeRelationPrincipalLocalization.fullEquiv (p).left (q).left s

/-- The comparison retains the actual geometric coefficient restriction. -/
theorem originalPrincipalFullInvariantEquiv_coefficients
    (a : compatibleFunctions (p).left (q).left) :
    (originalPrincipalFullInvariantEquiv f hL d V c k s
      (algebraMap _ (Localization.Away s) a)).val = (W).ι.appTop a.val :=
  SchemeRelationPrincipalLocalization.fullEquiv_algebraMap (p).left (q).left s a

/-- The full restricted invariant candidate maps to the original invariant candidate. -/
def originalPrincipalCandidateMap :
    target (SchemeRelationRestriction.fst (p).left (q).left (W).ι)
      (SchemeRelationRestriction.snd (p).left (q).left (W).ι) ⟶ target (p).left (q).left :=
  SchemeRelationPrincipalLocalization.candidateOpenMap (p).left (q).left s

instance originalPrincipalCandidateMap_isOpenImmersion :
    IsOpenImmersion (originalPrincipalCandidateMap f hL d V c k s) :=
  SchemeRelationPrincipalLocalization.candidateOpenMap_isOpenImmersion (p).left (q).left s

/-- The geometric source square commutes with its actual full-relation projection. -/
@[reassoc]
theorem originalPrincipalCandidateMap_projection :
    projection (SchemeRelationRestriction.fst (p).left (q).left (W).ι)
      (SchemeRelationRestriction.snd (p).left (q).left (W).ι) ≫
      originalPrincipalCandidateMap f hL d V c k s =
      (W).ι ≫ projection (p).left (q).left :=
  SchemeRelationPrincipalLocalization.candidateOpenMap_projection (p).left (q).left s

/-- The principal candidate retains the unchanged original coefficient-base structure. -/
def originalPrincipalRelativeModel : Over (Spec (.of R)) :=
  Over.mk (originalPrincipalCandidateMap f hL d V c k s ≫
    (invariantAffineModel f hL d V c k).hom)

/-- The principal invariant candidate embeds over the unchanged original coefficient base. -/
def originalPrincipalRelativeCandidateMap : originalPrincipalRelativeModel f hL d V c k s ⟶
    invariantAffineModel f hL d V c k :=
  Over.homMk (originalPrincipalCandidateMap f hL d V c k s) rfl

/-- The full restricted projection retains the original relative structure. -/
def originalPrincipalRelativeProjection : Over.mk ((W).ι ≫ A.hom) ⟶
    originalPrincipalRelativeModel f hL d V c k s :=
  Over.homMk (projection (SchemeRelationRestriction.fst (p).left (q).left (W).ι)
      (SchemeRelationRestriction.snd (p).left (q).left (W).ι)) (by
    change projection (SchemeRelationRestriction.fst (p).left (q).left (W).ι)
      (SchemeRelationRestriction.snd (p).left (q).left (W).ι) ≫
      originalPrincipalCandidateMap f hL d V c k s ≫
      (invariantAffineModel f hL d V c k).hom = (W).ι ≫ A.hom
    rw [← Category.assoc, originalPrincipalCandidateMap_projection, Category.assoc]
    exact congrArg (fun t ↦ (W).ι ≫ t) (invariantAffineProjection f hL d V c k).w)

/-- The full original projection square commutes over the original base. -/
@[reassoc]
theorem originalPrincipalRelativeCandidateMap_projection :
    originalPrincipalRelativeProjection f hL d V c k s ≫
      originalPrincipalRelativeCandidateMap f hL d V c k s =
      Over.homMk (W).ι rfl ≫ invariantAffineProjection f hL d V c k := by
  apply Over.OverMorphism.ext
  exact originalPrincipalCandidateMap_projection f hL d V c k s

end FLT.Mazur.HilbertChart.AffineRestriction
