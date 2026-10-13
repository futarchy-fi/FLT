/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.AffineHilbertFullFiberInterior
public import FLT.Mazur.AffineHilbertNestedRestriction

/-!
# Actual full-envelope charts for arbitrary etale translations

Restrict the original source to the maximal open full-fiber interior. Its
actual open chart parameter has a full original independent envelope, and
coefficient one is admissible there. Closed projections are unnecessary;
affineness and coverage of the constructed sources are not asserted.
-/

@[expose] public noncomputable section
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry Opposite
namespace FLT.Mazur.HilbertChart.AffineRestriction
open CartierAbel SchemePicard FCurve SchemeEffectiveEpiSections
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
variable {R : Type} [CommRing R] [Algebra.FiniteType ℤ R] {X : Scheme}
  (f : X ⟶ Spec (.of R)) [IsProper f] [Flat f] [GeometricallyIntegral f]
  [SmoothOfRelativeDimension 1 f] {L : X.Modules} (hL : AmpleLineBundle L)
  (d : ℕ) (V : Over (Spec (.of R)))
  (c : (relativeFppfSheaf f).obj.obj (op V))
  {A : Over (Spec (.of R))} (k : A ⟶ variableHilbertTest f d V)
  [IsOpenImmersion k.left]
local notation "U" => fullEnvelopeInterior f hL d V c k
local notation "π" => Over.Hom.left (prod.fst : prod A V ⟶ A)

/-- The source is the actual constructed full-fiber open, with its original structural map. -/
def fullInteriorSource : Over (Spec (.of R)) := Over.mk ((U).ι ≫ A.hom)

/-- The actual source inclusion, retaining the interior of the original full-fiber locus. -/
def fullInteriorSourceMap : fullInteriorSource f hL d V c k ⟶ A := Over.homMk (U).ι

local notation "u" => fullInteriorSourceMap f hL d V c k

/-- The new parameter is an actual open restriction of the original parameter. -/
@[irreducible]
def fullInteriorChart : fullInteriorSource f hL d V c k ⟶ variableHilbertTest f d V := u ≫ k

local notation "l" => fullInteriorChart f hL d V c k

instance fullInteriorChart_isOpenImmersion : IsOpenImmersion (l).left := by
  unfold fullInteriorChart fullInteriorSourceMap
  change IsOpenImmersion ((U).ι ≫ k.left)
  infer_instance

/-- The independent product of the new source is the original envelope restricted over it. -/
def fullInteriorProductIso : ((π) ⁻¹ᵁ U).toScheme ≅
    (prod (fullInteriorSource f hL d V c k) V).left :=
  (isPullback_morphismRestrict π U).flip.isoIsPullback _ _
    (((IsPullback.of_prod_fst_with_id u V).map (Over.forget _)).flip)

@[reassoc]
theorem fullInteriorProductIso_hom_map :
    (fullInteriorProductIso f hL d V c k).hom ≫ (prod.map u (𝟙 V)).left =
      ((π) ⁻¹ᵁ U).ι :=
  (isPullback_morphismRestrict π U).flip.isoIsPullback_hom_fst _ _
    (((IsPullback.of_prod_fst_with_id u V).map (Over.forget _)).flip)

variable [Etale V.hom]

/-- An actual isomorphism from the new FULL relation to its independent-translation envelope. -/
def fullInteriorRelationIso : (relation f hL d V c l).left ≅
    (prod (fullInteriorSource f hL d V c k) V).left := by
  unfold fullInteriorChart
  exact nestedSchemeDoubleIso f hL d V c k u ≪≫
    fullEnvelopeInteriorRelationIso f hL d V c k ≪≫ fullInteriorProductIso f hL d V c k

/-- The constructed isomorphism is the new chart's original envelope map. -/
theorem fullInteriorRelationIso_hom :
    (fullInteriorRelationIso f hL d V c k).hom = (toEnvelope f hL d V c l).left := by
  let _ : Mono u := by
    dsimp only [fullInteriorSourceMap]
    infer_instance
  apply (cancel_mono (prod.map u (𝟙 V)).left).mp
  dsimp only [fullInteriorRelationIso, Iso.trans_hom]
  unfold fullInteriorChart
  dsimp only [id, Iso.trans_hom]
  rw [Category.assoc, Category.assoc, fullInteriorProductIso_hom_map,
    fullEnvelopeInteriorRelationIso_hom_ι, ← Category.assoc]
  have hh := nestedSchemeDoubleIso_arrow f hL d V c k u
  change (nestedSchemeDoubleIso f hL d V c k u).hom ≫
    SchemeRelationRestriction.arrow (fst f hL d V c k).left
      (snd f hL d V c k).left (U).ι = (nestedToFullRelation f hL d V c k u).left at hh
  rw [hh]
  exact congrArg Over.Hom.left (nestedToFullRelation_envelope f hL d V c k u)

/-- Full-envelope effectiveness on the constructed source is proved, not supplied as a field. -/
instance fullInteriorChart_toEnvelope_isIso : IsIso (toEnvelope f hL d V c l).left := by
  rw [← fullInteriorRelationIso_hom f hL d V c k]
  infer_instance

/-- Coefficient one is now genuinely admissible on the constructed source. -/
theorem fullInteriorChart_denominators_eq_top :
    invariantEnvelopeDenominators f hL d V c l = ⊤ :=
  (invariantEnvelopeDenominators_eq_top_iff f hL d V c l).mpr inferInstance

/-- Each point of the constructed source has an explicit nonvanishing invariant coefficient. -/
theorem fullInteriorChart_nonvanishing (x : (fullInteriorSource f hL d V c k).left) :
    ∃ r : compatibleFunctions (fst f hL d V c l).left (snd f hL d V c l).left,
      r ∈ invariantEnvelopeDenominators f hL d V c l ∧
        x ∈ (fullInteriorSource f hL d V c k).left.basicOpen r.val := by
  refine ⟨1, ?_, ?_⟩
  · rw [fullInteriorChart_denominators_eq_top]
    trivial
  · change x ∈ (fullInteriorSource f hL d V c k).left.basicOpen 1
    simp only [Scheme.basicOpen_one, TopologicalSpace.Opens.mem_top]

end FLT.Mazur.HilbertChart.AffineRestriction
