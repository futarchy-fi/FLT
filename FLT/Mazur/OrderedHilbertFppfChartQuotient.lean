/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.OrderedHilbertFppfChartKernel
public import FLT.Mazur.OrderedHilbertChartInvariantComparison

/-!
# Scheme effectivity of the full original restriction along fppf translations

The constructed composite cover makes the entire original restricted relation
effective as a scheme quotient. It gives all invariant functions, agrees with
the parameter comparison, and embeds the resulting scheme openly into the old
quotient whenever the translation base is smooth.
-/

@[expose] public noncomputable section
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry Opposite
namespace FLT.Mazur.OrderedHilbertBaseOpenChart
open HilbertChart CartierAbel SchemePicard FCurve RelativeRelationOrbit
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
variable {R : Type} [CommRing R] [Algebra.FiniteType ℤ R] {X : Scheme}
  (f : X ⟶ Spec (.of R)) [IsProper f] [Flat f] [GeometricallyIntegral f]
  [SmoothOfRelativeDimension 1 f] {L : X.Modules} (hL : AmpleLineBundle L)
  (d : ℕ) {V W : Over (Spec (.of R))} (b : W ⟶ V)
  [IsOpenImmersion V.hom] [Flat b.left] [LocallyOfFinitePresentation b.left]
  [Surjective b.left] (c : (relativeFppfSheaf f).obj.obj (op V))
local notation "cW" => CategoryTheory.Functor.map
  (ObjectProperty.FullSubcategory.obj (relativeFppfSheaf f)) (Quiver.Hom.op b) c
local notation "e" => fullRestrictedEquivalence f hL d W cW
local notation "g" => fppfChartProjection f hL d b c
local notation "H" => fppfChartProjection_isPullback f hL d b c

/-- All original restricted invariants have the constructed target scheme as model. -/
def fppfFullInvariantIso : invariantLocallyRingedSpace e ≅
    (variableHilbertTest f d V).left.toLocallyRingedSpace :=
  fppfInvariantQuotientIso e g H

/-- The quotient model preserves the actual composite projection from the full source. -/
@[reassoc]
theorem fppfFullInvariantIso_projection :
    invariantLocallyRingedProjection e ≫ (fppfFullInvariantIso f hL d b c).hom =
      (g).left.toLRSHom := fppfInvariantQuotientIso_projection e g H

/-- The coefficient morphism is the original invariant coefficient morphism. -/
theorem fppfFullInvariantIso_base :
    (fppfFullInvariantIso f hL d b c).hom ≫
      (variableHilbertTest f d V).hom.toLRSHom = invariantLocallyRingedBaseMap e :=
  fppfInvariantQuotientIso_baseMap e g H

/-- The scheme also satisfies the full original scheme coequalizer universal property. -/
def fppfFullCoforkIsColimit : IsColimit (Cofork.ofπ (g).left
    (congrArg Over.Hom.left (H).w)) :=
  isColimitCoforkOfEffectiveEpi (g).left _ ((H).map (Over.forget _)).isLimit

/-- Direct effectivity agrees with descent through the entire parameter relation. -/
theorem fppfFullInvariantIso_comparison :
    (fppfFullInvariantIso f hL d b c).hom =
      (fullInvariantComparisonIso f hL d W cW).hom ≫
        (variableHilbertFppfQuotientIso f hL d b c).hom := by
  let _ : Epi (invariantLocallyRingedProjection e) := by
    unfold invariantLocallyRingedProjection locallyRingedProjection
    infer_instance
  apply (cancel_epi (invariantLocallyRingedProjection e)).mp
  rw [fppfFullInvariantIso_projection, fullInvariantComparisonIso_source_assoc,
    variableHilbertFppfQuotientIso_projection]
  rfl

variable [Smooth W.hom]

/-- The effective scheme is an actual open neighborhood in the old original quotient. -/
def fppfFullSchemeNeighborhood :
    (variableHilbertTest f d V).left.toLocallyRingedSpace ⟶
      invariantLocallyRingedSpace (smoothHilbertEquivalenceRelation f hL) :=
  (fppfFullInvariantIso f hL d b c).inv ≫ fullOriginalQuotientInclusion f hL d W cW

instance fppfFullSchemeNeighborhood_isOpenImmersion :
    LocallyRingedSpace.IsOpenImmersion (fppfFullSchemeNeighborhood f hL d b c) := by
  dsimp only [fppfFullSchemeNeighborhood]
  infer_instance

/-- The open neighborhood retains the original coefficient scheme map. -/
theorem fppfFullSchemeNeighborhood_base :
    fppfFullSchemeNeighborhood f hL d b c ≫
      invariantLocallyRingedBaseMap (smoothHilbertEquivalenceRelation f hL) =
        (variableHilbertTest f d V).hom.toLRSHom := by
  dsimp only [fppfFullSchemeNeighborhood]
  rw [Category.assoc, fullOriginalQuotientInclusion_base,
    ← fppfFullInvariantIso_base, Iso.inv_hom_id_assoc]

/-- The constructed scheme exhausts this entire full original quotient neighborhood. -/
theorem fppfFullSchemeNeighborhood_range :
    Set.range (fppfFullSchemeNeighborhood f hL d b c).base =
      (smoothTranslationOrbitOpen f hL d W cW :
        Set (Orbit (smoothHilbertEquivalenceRelation f hL))) := by
  have hs : Function.Surjective (fppfFullInvariantIso f hL d b c).inv.base :=
    (TopCat.homeoOfIso (LocallyRingedSpace.forgetToTop.mapIso
      (fppfFullInvariantIso f hL d b c).symm)).surjective
  change Set.range ((fullOriginalQuotientInclusion f hL d W cW).base ∘
    (fppfFullInvariantIso f hL d b c).inv.base) = _
  rw [Set.range_comp, hs.range_eq]
  simpa only [Set.image_univ] using fullOriginalQuotientInclusion_range f hL d W cW

end FLT.Mazur.OrderedHilbertBaseOpenChart
