/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.AffineHilbertFullFiberOpen
public import FLT.Mazur.AffineHilbertNestedRestriction

/-!
# Actual chart restrictions constructed from the full-fiber open

The constructed source has an open chart parameter and its complete original
relation fills its independent envelope. Thus coefficient one is admissible on
this new source. Affineness of that source and coverage by such sources remain
separate; neither follows merely from the openness proved here.
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
  (hπ : IsClosedMap (Over.Hom.left (prod.fst : prod A V ⟶ A)))
local notation "U" => fullEnvelopeOpen f hL d V c k hπ
local notation "π" => Over.Hom.left (prod.fst : prod A V ⟶ A)

/-- The source is the actual constructed full-fiber open, with its original structural map. -/
def fullFiberSource : Over (Spec (.of R)) := Over.mk ((U).ι ≫ A.hom)

/-- The actual source inclusion, retaining every point whose full original fiber is present. -/
def fullFiberSourceMap : fullFiberSource f hL d V c k hπ ⟶ A := Over.homMk (U).ι

local notation "u" => fullFiberSourceMap f hL d V c k hπ

/-- The new parameter is an actual open restriction of the original parameter. -/
@[irreducible]
def fullFiberChart : fullFiberSource f hL d V c k hπ ⟶ variableHilbertTest f d V := u ≫ k

local notation "l" => fullFiberChart f hL d V c k hπ

instance fullFiberChart_isOpenImmersion : IsOpenImmersion (l).left := by
  unfold fullFiberChart fullFiberSourceMap
  change IsOpenImmersion ((U).ι ≫ k.left)
  infer_instance

/-- The independent product of the new source is the original envelope restricted over it. -/
def fullFiberProductIso : ((π) ⁻¹ᵁ U).toScheme ≅
    (prod (fullFiberSource f hL d V c k hπ) V).left :=
  (isPullback_morphismRestrict π U).flip.isoIsPullback _ _
    (((IsPullback.of_prod_fst_with_id u V).map (Over.forget _)).flip)

@[reassoc]
theorem fullFiberProductIso_hom_map :
    (fullFiberProductIso f hL d V c k hπ).hom ≫ (prod.map u (𝟙 V)).left =
      ((π) ⁻¹ᵁ U).ι :=
  (isPullback_morphismRestrict π U).flip.isoIsPullback_hom_fst _ _
    (((IsPullback.of_prod_fst_with_id u V).map (Over.forget _)).flip)

/-- An actual isomorphism from the new FULL relation to its independent-translation envelope. -/
def fullFiberRelationIso : (relation f hL d V c l).left ≅
    (prod (fullFiberSource f hL d V c k hπ) V).left := by
  unfold fullFiberChart
  exact nestedSchemeDoubleIso f hL d V c k u ≪≫
    fullEnvelopeOpenRelationIso f hL d V c k hπ ≪≫ fullFiberProductIso f hL d V c k hπ

/-- The constructed isomorphism is the new chart's original envelope map. -/
theorem fullFiberRelationIso_hom :
    (fullFiberRelationIso f hL d V c k hπ).hom = (toEnvelope f hL d V c l).left := by
  let _ : Mono u := by
    dsimp only [fullFiberSourceMap]
    infer_instance
  apply (cancel_mono (prod.map u (𝟙 V)).left).mp
  dsimp only [fullFiberRelationIso, Iso.trans_hom]
  unfold fullFiberChart
  dsimp only [id, Iso.trans_hom]
  rw [Category.assoc, Category.assoc, fullFiberProductIso_hom_map,
    fullEnvelopeOpenRelationIso_hom_ι, ← Category.assoc]
  have hh := nestedSchemeDoubleIso_arrow f hL d V c k u
  change (nestedSchemeDoubleIso f hL d V c k u).hom ≫
    SchemeRelationRestriction.arrow (fst f hL d V c k).left
      (snd f hL d V c k).left (U).ι = (nestedToFullRelation f hL d V c k u).left at hh
  rw [hh]
  exact congrArg Over.Hom.left (nestedToFullRelation_envelope f hL d V c k u)

/-- Full-envelope effectiveness on the constructed source is proved, not supplied as a field. -/
instance fullFiberChart_toEnvelope_isIso : IsIso (toEnvelope f hL d V c l).left := by
  rw [← fullFiberRelationIso_hom f hL d V c k hπ]
  infer_instance

/-- Coefficient one is now genuinely admissible on the constructed source. -/
theorem fullFiberChart_denominators_eq_top :
    invariantEnvelopeDenominators f hL d V c l = ⊤ :=
  (invariantEnvelopeDenominators_eq_top_iff f hL d V c l).mpr inferInstance

/-- Each point of the constructed source has an explicit nonvanishing invariant coefficient. -/
theorem fullFiberChart_nonvanishing (x : (fullFiberSource f hL d V c k hπ).left) :
    ∃ r : compatibleFunctions (fst f hL d V c l).left (snd f hL d V c l).left,
      r ∈ invariantEnvelopeDenominators f hL d V c l ∧
        x ∈ (fullFiberSource f hL d V c k hπ).left.basicOpen r.val := by
  refine ⟨1, ?_, ?_⟩
  · rw [fullFiberChart_denominators_eq_top]
    trivial
  · change x ∈ (fullFiberSource f hL d V c k hπ).left.basicOpen 1
    simp only [Scheme.basicOpen_one, TopologicalSpace.Opens.mem_top]

end FLT.Mazur.HilbertChart.AffineRestriction
