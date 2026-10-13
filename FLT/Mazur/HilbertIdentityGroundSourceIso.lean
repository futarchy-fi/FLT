/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.HilbertIdentityGroundOriginalQuotient

/-!
# Recovering the original source from the identity-ground quotient

The effective refined affine quotient is isomorphic to the original parameter
source. Its map to the original invariant quotient is exactly the old source
projection through this isomorphism. In particular the old full relation must
still be imposed; it is not replaced by the refined diagonal relation.
-/

@[expose] public noncomputable section
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry Opposite
namespace FLT.Mazur.HilbertChart.AffineRestriction
open CartierAbel SchemePicard FCurve RelativeRelationOrbit
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
variable {R : Type} [CommRing R] [Algebra.FiniteType ℤ R] {X : Scheme}
  (f : X ⟶ Spec (.of R)) [IsProper f] [Flat f] [GeometricallyIntegral f]
  [SmoothOfRelativeDimension 1 f] {L : X.Modules} (hL : AmpleLineBundle L)
  (d : ℕ) (V : Over (Spec (.of R))) [IsAffine V.left] [Etale V.hom]
  (c : (relativeFppfSheaf f).obj.obj (op V))
  {A : Over (Spec (.of R))} [IsAffine A.left] (k : A ⟶ variableHilbertTest f d V)
  [IsOpenImmersion k.left]
local instance : Algebra.FiniteType ℤ Γ(V.left, ⊤) :=
  AffineEtaleIdentityGroundBase.coefficient_finiteType V
local notation "a" => AffineEtaleIdentityGroundBase.base V
local notation "W" => AffineEtaleIdentityGroundBase.translation V
local notation "t" => AffineEtaleIdentityGroundBase.comparison V
local notation "q" => Limits.pullback.snd f a
local instance : SmoothOfRelativeDimension 1 q :=
  MorphismProperty.pullback_snd _ _ inferInstance
local notation "u" => groundBaseSourceMap f a hL d V W t k
local notation "l" => groundBaseSourceChart f a hL d V W t k
local notation "h'" => fixedBaseAmple f a hL
local notation "c'" => fixedBaseTranslationClass f a V W t c
local notation "e" => variableChartEquivalenceRelation f hL d V c

local instance : IsIso (W).hom := inferInstanceAs (IsIso (𝟙 _))

/-- Identity translation makes the constructed effective projection an isomorphism. -/
instance identityGroundProjection_isIso : IsIso (fullEnvelopeProjection q h' d W c' l) :=
  (fullEnvelope_isPullback q h' d W c' l).isIso_fst_of_isIso

/-- The constructed affine quotient recovers the original scheme parameter source. -/
def identityGroundQuotientSourceIso : fullEnvelopeScheme q h' d W c' l ≅ A.left :=
  (asIso (fullEnvelopeProjection q h' d W c' l)).symm ≪≫ asIso (u).left

/-- The source comparison recovers exactly the original source point, as a scheme morphism. -/
@[reassoc]
theorem identityGroundQuotientSourceIso_projection :
    fullEnvelopeProjection q h' d W c' l ≫
      (identityGroundQuotientSourceIso f hL d V c k).hom = (u).left := by
  simp only [identityGroundQuotientSourceIso, Iso.trans_hom, Iso.symm_hom, asIso_inv,
    asIso_hom, IsIso.hom_inv_id_assoc]

/-- The map to the original quotient retains the original projection as a locally ringed map. -/
@[reassoc]
theorem identityGroundOriginalQuotientMap_source :
    (fullEnvelopeProjection q h' d W c' l).toLRSHom ≫
      identityGroundOriginalQuotientMap f hL d V c k =
        (u).left.toLRSHom ≫ k.left.toLRSHom ≫ invariantLocallyRingedProjection e := by
  rw [identityGroundOriginalQuotientMap, ← Category.assoc, fullEnvelopeOpenChart_source,
    Category.assoc, variableChartFixedBaseQuotientMap_projection]
  rw [← Scheme.Hom.comp_toLRSHom_assoc, ← Scheme.Hom.comp_toLRSHom_assoc]
  have hs : (u).left ≫ k.left = (l).left ≫
      (variableHilbertFixedBaseProjection f a hL d V W t).left :=
    congrArg Over.Hom.left (groundBaseSource_square f a hL d V W t k)
  rw [← hs]

/-- The new affine source carries the old quotient map, not a replacement equivalence relation. -/
theorem identityGroundOriginalQuotientMap_eq :
    identityGroundOriginalQuotientMap f hL d V c k =
      (identityGroundQuotientSourceIso f hL d V c k).hom.toLRSHom ≫
        k.left.toLRSHom ≫ invariantLocallyRingedProjection e := by
  apply (cancel_epi (fullEnvelopeProjection q h' d W c' l).toLRSHom).mp
  rw [identityGroundOriginalQuotientMap_source]
  conv_rhs => rw [← Scheme.Hom.comp_toLRSHom_assoc, identityGroundQuotientSourceIso_projection]

/-- The quotient comparison is topologically open and retains the old relation fibers. -/
theorem identityGroundOriginalQuotientMap_isOpenMap :
    IsOpenMap (identityGroundOriginalQuotientMap f hL d V c k).base := by
  rw [identityGroundOriginalQuotientMap_eq, LocallyRingedSpace.comp_base,
    LocallyRingedSpace.comp_base, invariantLocallyRingedProjection_base]
  change IsOpenMap (fun x ↦ projection e
    (k.left ((identityGroundQuotientSourceIso f hL d V c k).hom x)))
  exact ((projection_isOpenMap e (variableChartRelationSnd f hL d V c).left.isOpenMap).comp
    k.left.isOpenMap).comp (identityGroundQuotientSourceIso f hL d V c k).hom.isOpenMap

end FLT.Mazur.HilbertChart.AffineRestriction
