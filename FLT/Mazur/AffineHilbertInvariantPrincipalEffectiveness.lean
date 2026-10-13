/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.AffineHilbertInvariantPrincipalProduct
public import FLT.Mazur.AffineHilbertNestedRestriction
public import FLT.Mazur.AffineHilbertEnvelopeOpenChart

/-!
# Effective Hilbert quotients on admissible invariant principal sources

An actual member of the constructed denominator ideal proves that the
refined chart's original toEnvelope map is invertible. The full-envelope
quotient construction can then be applied without an effectiveness input.
The existence of enough admissible coefficients remains separate.
-/

@[expose] public noncomputable section
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry Opposite
namespace FLT.Mazur.HilbertChart.AffineRestriction
open CartierAbel SchemePicard FCurve SchemeEffectiveEpiSections RelativeRelationOrbit
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

variable (r : compatibleFunctions (AffineRestriction.fst f hL d V c k).left
  (AffineRestriction.snd f hL d V c k).left)
  (hr : r ∈ invariantEnvelopeDenominators f hL d V c k)
local notation "u" => invariantPrincipalSourceMap f hL d V c k r

/-- The actual refined chart map, sealed to retain its source during elaboration. -/
@[irreducible]
def invariantPrincipalChart : invariantPrincipalSource f hL d V c k r ⟶
    variableHilbertTest f d V :=
  (invariantPrincipalSourceMap f hL d V c k r) ≫ k

local notation "k'" => invariantPrincipalChart f hL d V c k r

/-- The refined map is the actual composite of the two original open immersions. -/
instance invariantPrincipalChart_isOpenImmersion : IsOpenImmersion (k').left := by
  unfold invariantPrincipalChart invariantPrincipalSourceMap
  change IsOpenImmersion ((A.left.basicOpen r.val).ι ≫ k.left)
  infer_instance

/-- The actual refined chart relation fills its actual independent-translation product. -/
def invariantPrincipalFullEnvelopeIso : (relation f hL d V c k').left ≅
    (prod (invariantPrincipalSource f hL d V c k r) V).left :=
  by
    unfold invariantPrincipalChart
    exact nestedSchemeDoubleIso f hL d V c k u ≪≫
      invariantPrincipalProductIso f hL d V c k r hr

/-- The constructed isomorphism is exactly the original refined envelope inclusion. -/
theorem invariantPrincipalFullEnvelopeIso_hom :
    (invariantPrincipalFullEnvelopeIso f hL d V c k r hr).hom =
      (toEnvelope f hL d V c k').left := by
  let _ : Mono u := by
    dsimp only [invariantPrincipalSourceMap]
    infer_instance
  apply (cancel_mono (prod.map u (𝟙 V)).left).mp
  dsimp only [invariantPrincipalFullEnvelopeIso, Iso.trans_hom]
  unfold invariantPrincipalChart
  dsimp only [id, Iso.trans_hom]
  have hh := nestedSchemeDoubleIso_arrow f hL d V c k u
  change (nestedSchemeDoubleIso f hL d V c k u).hom ≫
    SchemeRelationRestriction.arrow (p).left (q).left (A.left.basicOpen r.val).ι =
      (nestedToFullRelation f hL d V c k u).left at hh
  rw [Category.assoc, invariantPrincipalProductIso_hom_map, ← Category.assoc, hh]
  exact congrArg Over.Hom.left (nestedToFullRelation_envelope f hL d V c k u)

include hr in
/-- Effectiveness of the refined envelope is proved from the actual coefficient membership. -/
theorem invariantPrincipal_toEnvelope_isIso : IsIso (toEnvelope f hL d V c k').left := by
  rw [← invariantPrincipalFullEnvelopeIso_hom f hL d V c k r hr]
  infer_instance

variable [IsAffine A.left] [IsAffine V.left]

/-- The constructed invariant spectrum for this admissible principal source. -/
def invariantPrincipalQuotientScheme : Scheme :=
  let _ := invariantPrincipal_toEnvelope_isIso f hL d V c k r hr
  fullEnvelopeScheme f hL d V c k'

/-- Faithful flatness of translation identifies the ORIGINAL invariant LRS with that scheme. -/
def invariantPrincipalQuotientIso [Flat V.hom] [Surjective V.hom] :
    invariantLocallyRingedSpace (equivalence f hL d V c k') ≅
      (invariantPrincipalQuotientScheme f hL d V c k r hr).toLocallyRingedSpace :=
  let _ := invariantPrincipal_toEnvelope_isIso f hL d V c k r hr
  fullEnvelopeInvariantQuotientIso f hL d V c k'

/-- The constructed principal quotient is an open chart in the original invariant LRS. -/
def invariantPrincipalOpenChart [Etale V.hom] [Surjective V.hom] :
    (invariantPrincipalQuotientScheme f hL d V c k r hr).toLocallyRingedSpace ⟶
      invariantLocallyRingedSpace (variableChartEquivalenceRelation f hL d V c) :=
  let _ := invariantPrincipal_toEnvelope_isIso f hL d V c k r hr
  fullEnvelopeOpenChart f hL d V c k'

/-- This is an actual open immersion, including the entire invariant structure sheaf. -/
instance invariantPrincipalOpenChart_isOpenImmersion [Etale V.hom] [Surjective V.hom] :
    LocallyRingedSpace.IsOpenImmersion (invariantPrincipalOpenChart f hL d V c k r hr) := by
  let _ := invariantPrincipal_toEnvelope_isIso f hL d V c k r hr
  dsimp only [invariantPrincipalOpenChart]
  infer_instance

end FLT.Mazur.HilbertChart.AffineRestriction
