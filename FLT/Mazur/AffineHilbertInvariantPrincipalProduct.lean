/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.AffineHilbertInvariantEnvelope

/-!
# Actual product envelopes on admissible invariant principal sources

The full double relation is identified with the product of the principal
source and the unchanged independent translation. Both the original arrow
and translation coordinates are retained. No coverage of these opens is claimed.
-/

@[expose] public noncomputable section
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry Opposite
namespace FLT.Mazur.HilbertChart.AffineRestriction
open CartierAbel SchemePicard FCurve SchemeEffectiveEpiSections SchemeOpenEnvelope
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
variable {R : Type} [CommRing R] [Algebra.FiniteType ℤ R] {X : Scheme}
  (f : X ⟶ Spec (.of R)) [IsProper f] [Flat f] [GeometricallyIntegral f]
  [SmoothOfRelativeDimension 1 f] {L : X.Modules} (hL : AmpleLineBundle L)
  (d : ℕ) (V : Over (Spec (.of R)))
  (c : (relativeFppfSheaf f).obj.obj (op V))
  {A : Over (Spec (.of R))} (k : A ⟶ variableHilbertTest f d V)
  [IsOpenImmersion k.left]
local notation "p" => fst f hL d V c k
local notation "q" => snd f hL d V c k

local notation "j" => Over.Hom.left (toEnvelope f hL d V c k)
local notation "π" => Over.Hom.left (prod.fst : prod A V ⟶ A)
local notation "C" => compatibleFunctions (Over.Hom.left p) (Over.Hom.left q)

/-- The principal source retains the original coefficient base map. -/
def invariantPrincipalSource (r : C) : Over (Spec (.of R)) :=
  Over.mk ((A.left.basicOpen r.val).ι ≫ A.hom)

/-- The unchanged principal inclusion in the original relative source. -/
def invariantPrincipalSourceMap (r : C) : invariantPrincipalSource f hL d V c k r ⟶ A :=
  Over.homMk (A.left.basicOpen r.val).ι

/-- The product with independent translation is exactly the inverse-image envelope open. -/
def invariantPrincipalProductOpenIso (r : C) :
    ((π) ⁻¹ᵁ A.left.basicOpen r.val).toScheme ≅
      (prod (invariantPrincipalSource f hL d V c k r) V).left :=
  (isPullback_morphismRestrict π (A.left.basicOpen r.val)).flip.isoIsPullback _ _
    (((IsPullback.of_prod_fst_with_id (invariantPrincipalSourceMap f hL d V c k r) V).map
      (Over.forget _)).flip)

omit [IsOpenImmersion k.left] in
/-- This product identification retains its actual map to the original envelope. -/
@[reassoc]
theorem invariantPrincipalProductOpenIso_hom_map (r : C) :
    (invariantPrincipalProductOpenIso f hL d V c k r).hom ≫
        (prod.map (invariantPrincipalSourceMap f hL d V c k r) (𝟙 V)).left =
      ((π) ⁻¹ᵁ A.left.basicOpen r.val).ι :=
    (isPullback_morphismRestrict π (A.left.basicOpen r.val)).flip.isoIsPullback_hom_fst _ _
      (((IsPullback.of_prod_fst_with_id (invariantPrincipalSourceMap f hL d V c k r) V).map
        (Over.forget _)).flip)

/-- An admissible coefficient fills the actual tensor product envelope of its principal source. -/
def invariantPrincipalProductIso (r : C)
    (hr : r ∈ invariantEnvelopeDenominators f hL d V c k) :
    SchemeRelationRestriction.doubleDomain (p).left (q).left (A.left.basicOpen r.val).ι ≅
      (prod (invariantPrincipalSource f hL d V c k r) V).left :=
  invariantPrincipalEnvelopeIso f hL d V c k r hr ≪≫
    invariantPrincipalProductOpenIso f hL d V c k r

/-- The complete relation arrow is preserved under this product-envelope isomorphism. -/
@[reassoc]
theorem invariantPrincipalProductIso_hom_map (r : C)
    (hr : r ∈ invariantEnvelopeDenominators f hL d V c k) :
    (invariantPrincipalProductIso f hL d V c k r hr).hom ≫
        (prod.map (invariantPrincipalSourceMap f hL d V c k r) (𝟙 V)).left =
      SchemeRelationRestriction.arrow (p).left (q).left (A.left.basicOpen r.val).ι ≫ j := by
  rw [invariantPrincipalProductIso, Iso.trans_hom, Category.assoc,
    invariantPrincipalProductOpenIso_hom_map, invariantPrincipalEnvelopeIso_hom_ι]

omit [IsOpenImmersion k.left] in
/-- The refined source is genuinely affine when the original source is affine. -/
instance invariantPrincipalSource_affine [IsAffine A.left] (r : C) :
    IsAffine (invariantPrincipalSource f hL d V c k r).left :=
  (isAffineOpen_top A.left).basicOpen r.val

/-- The actual full original restricted relation is affine on an admissible principal source. -/
theorem invariantPrincipalRelation_affine [IsAffine A.left] [IsAffine V.left] (r : C)
    (hr : r ∈ invariantEnvelopeDenominators f hL d V c k) :
    IsAffine (SchemeRelationRestriction.doubleDomain (p).left (q).left
      (A.left.basicOpen r.val).ι) := by
  let _ := variableHilbertOverlap_envelope_affine V
    (invariantPrincipalSource f hL d V c k r)
  exact IsAffine.of_isIso (invariantPrincipalProductIso f hL d V c k r hr).hom

end FLT.Mazur.HilbertChart.AffineRestriction
