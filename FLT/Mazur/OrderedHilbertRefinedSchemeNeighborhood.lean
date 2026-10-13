/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.VariableHilbertRefinedSchemeModel
public import FLT.Mazur.OrderedHilbertChartInvariantComparison

/-!
# Refined effective models give full original scheme neighborhoods

Effectivity after arbitrary fppf translation refinement produces an actual
projection from the entire original source restriction, with its full kernel
pair, and a scheme neighborhood in the old quotient when the base is smooth.
The existence of effective refined models is not assumed as a record field.
-/

@[expose] public noncomputable section
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry Opposite
namespace FLT.Mazur.OrderedHilbertBaseOpenChart
open HilbertChart CartierAbel SchemePicard FCurve RelativeRelationOrbit
open VariableHilbertFppfRefinement
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
variable {R : Type} [CommRing R] [Algebra.FiniteType ℤ R] {X : Scheme}
  (f : X ⟶ Spec (.of R)) [IsProper f] [Flat f] [GeometricallyIntegral f]
  [SmoothOfRelativeDimension 1 f] {L : X.Modules} (hL : AmpleLineBundle L)
  (d : ℕ) {V W : Over (Spec (.of R))} (b : W ⟶ V)
  (c : (relativeFppfSheaf f).obj.obj (op V))
  [Flat b.left] [LocallyOfFinitePresentation b.left] [Surjective b.left]
  {Z : Over (Spec (.of R))} (π : variableHilbertTest f d W ⟶ Z)
  (H : IsPullback
    (variableChartRelationFst f hL d W ((relativeFppfSheaf f).obj.map b.op c))
    (variableChartRelationSnd f hL d W ((relativeFppfSheaf f).obj.map b.op c)) π π)
local notation "e" => fullRestrictedEquivalence f hL d V c
local notation "P" => restrictedFst f hL d V c
local notation "Q" => restrictedSnd f hL d V c
local notation "s" => OrderedHilbertIdentityOriginalSection.sourceSection f hL

/-- The full original source maps to the refined model through the descended scheme projection. -/
def refinedModelFullProjection : source f hL d V c ⟶ Z :=
  projection f hL d V c ≫ descendedProjection f hL d b c π H.w

/-- Equality in the model retains precisely the original full-source Picard classes. -/
theorem refinedModelFullProjection_eq_iff {T : Over (Spec (.of R))}
    (a a' : T ⟶ source f hL d V c) :
    a ≫ refinedModelFullProjection f hL d b c π H =
        a' ≫ refinedModelFullProjection f hL d b c π H ↔
      (relativeFppfSheaf f).obj.map (a ≫ inclusion f hL d V c).op s =
        (relativeFppfSheaf f).obj.map (a' ≫ inclusion f hL d V c).op s := by
  rw [full_parameter_class, full_parameter_class]
  simpa only [refinedModelFullProjection, Category.assoc] using
    descendedProjection_eq_iff f hL d b c π H
      (a ≫ projection f hL d V c) (a' ≫ projection f hL d V c)

/-- The actual projection coequalizes the entire original restricted relation. -/
theorem refinedModelFullProjection_condition :
    P ≫ refinedModelFullProjection f hL d b c π H =
      Q ≫ refinedModelFullProjection f hL d b c π H :=
  (refinedModelFullProjection_eq_iff f hL d b c π H _ _).mpr
    (full_restricted_class f hL d V c)

/-- The entire original restricted relation is the scheme kernel pair of the model projection. -/
theorem refinedModelFullProjection_isPullback :
    IsPullback P Q (refinedModelFullProjection f hL d b c π H)
      (refinedModelFullProjection f hL d b c π H) := by
  let lift (z : PullbackCone (refinedModelFullProjection f hL d b c π H)
      (refinedModelFullProjection f hL d b c π H)) :=
    full_restricted_lift f hL d V c z.fst z.snd
      ((refinedModelFullProjection_eq_iff f hL d b c π H _ _).mp z.condition)
  exact IsPullback.of_isLimit (PullbackCone.IsLimit.mk
    (refinedModelFullProjection_condition f hL d b c π H) (fun z ↦ (lift z).choose)
    (fun z ↦ (lift z).choose_spec.1.1) (fun z ↦ (lift z).choose_spec.1.2)
    (fun z k h₁ h₂ ↦ (lift z).choose_spec.2 k ⟨h₁, h₂⟩))

variable [Flat π.left] [LocallyOfFinitePresentation π.left] [Surjective π.left]

/-- The full original invariant structure sheaf is the refined model's structure sheaf. -/
def refinedModelFullInvariantIso : invariantLocallyRingedSpace e ≅ Z.left.toLocallyRingedSpace :=
  fullInvariantComparisonIso f hL d V c ≪≫ descendedInvariantIso f hL d b c π H

/-- The model comparison recovers its actual map from the full original source. -/
@[reassoc]
theorem refinedModelFullInvariantIso_projection :
    invariantLocallyRingedProjection e ≫ (refinedModelFullInvariantIso f hL d b c π H).hom =
      (refinedModelFullProjection f hL d b c π H).left.toLRSHom := by
  dsimp only [refinedModelFullInvariantIso, Iso.trans_hom]
  rw [fullInvariantComparisonIso_source_assoc, descendedInvariantIso_projection]
  rfl

/-- All invariant coefficients retain the original base morphism. -/
theorem refinedModelFullInvariantIso_base :
    (refinedModelFullInvariantIso f hL d b c π H).hom ≫ Z.hom.toLRSHom =
      invariantLocallyRingedBaseMap e := by
  dsimp only [refinedModelFullInvariantIso, Iso.trans_hom]
  rw [Category.assoc, descendedInvariantIso_base, fullInvariantComparisonIso_base]

variable [Smooth V.hom]

/-- The refined effective model gives an actual open scheme neighborhood of the old quotient. -/
def refinedModelSchemeNeighborhood : Z.left.toLocallyRingedSpace ⟶
    invariantLocallyRingedSpace (smoothHilbertEquivalenceRelation f hL) :=
  (refinedModelFullInvariantIso f hL d b c π H).inv ≫
    fullOriginalQuotientInclusion f hL d V c

instance refinedModelSchemeNeighborhood_isOpenImmersion :
    LocallyRingedSpace.IsOpenImmersion (refinedModelSchemeNeighborhood f hL d b c π H) := by
  dsimp only [refinedModelSchemeNeighborhood]
  infer_instance

/-- The actual neighborhood preserves the original coefficient map. -/
theorem refinedModelSchemeNeighborhood_base :
    refinedModelSchemeNeighborhood f hL d b c π H ≫
      invariantLocallyRingedBaseMap (smoothHilbertEquivalenceRelation f hL) =
        Z.hom.toLRSHom := by
  dsimp only [refinedModelSchemeNeighborhood]
  rw [Category.assoc, fullOriginalQuotientInclusion_base,
    ← refinedModelFullInvariantIso_base f hL d b c π H, Iso.inv_hom_id_assoc]

/-- All points of the original full quotient neighborhood are retained. -/
theorem refinedModelSchemeNeighborhood_range :
    Set.range (refinedModelSchemeNeighborhood f hL d b c π H).base =
      (smoothTranslationOrbitOpen f hL d V c :
        Set (Orbit (smoothHilbertEquivalenceRelation f hL))) := by
  have hs : Function.Surjective (refinedModelFullInvariantIso f hL d b c π H).inv.base :=
    (TopCat.homeoOfIso (LocallyRingedSpace.forgetToTop.mapIso
      (refinedModelFullInvariantIso f hL d b c π H).symm)).surjective
  change Set.range ((fullOriginalQuotientInclusion f hL d V c).base ∘
    (refinedModelFullInvariantIso f hL d b c π H).inv.base) = _
  rw [Set.range_comp, hs.range_eq]
  simpa only [Set.image_univ] using fullOriginalQuotientInclusion_range f hL d V c

end FLT.Mazur.OrderedHilbertBaseOpenChart
