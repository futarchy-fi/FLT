/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.OrderedHilbertFppfChartQuotient
public import FLT.Mazur.RelativePicardFppfSingletonDescent

/-!
# Constructing effective chart quotients from translation compatibility

The input is equality of an original translating section on the actual
fppf base kernel pair. Descent constructs its target section and then a
scheme quotient of the full original restricted relation. No descended
section, splitting, quotient scheme, or effective projection is assumed.
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
  [Surjective b.left] (c : (relativeFppfSheaf f).obj.obj (op W))
  (hc : (relativeFppfSheaf f).obj.map (pullback.fst b b).op c =
    (relativeFppfSheaf f).obj.map (pullback.snd b b).op c)

include hc in
/-- Base compatibility constructs an actual fppf projection with the entire original kernel. -/
theorem compatibleTranslation_exists_fppfProjection :
    ∃ g : source f hL d W c ⟶ variableHilbertTest f d V,
      Flat g.left ∧ LocallyOfFinitePresentation g.left ∧ Surjective g.left ∧
        IsPullback (restrictedFst f hL d W c) (restrictedSnd f hL d W c) g g := by
  obtain ⟨t, ht, _⟩ := relativePicardFppf_singleton_existsUnique f b c hc
  subst c
  exact ⟨fppfChartProjection f hL d b t, inferInstance, inferInstance, inferInstance,
    fppfChartProjection_isPullback f hL d b t⟩

include hc in
/-- Compatibility constructs the full invariant scheme model with its original base map. -/
theorem compatibleTranslation_exists_invariantIso :
    ∃ e : invariantLocallyRingedSpace (fullRestrictedEquivalence f hL d W c) ≅
        (variableHilbertTest f d V).left.toLocallyRingedSpace,
      e.hom ≫ (variableHilbertTest f d V).hom.toLRSHom =
        invariantLocallyRingedBaseMap (fullRestrictedEquivalence f hL d W c) := by
  obtain ⟨t, ht, _⟩ := relativePicardFppf_singleton_existsUnique f b c hc
  subst c
  exact ⟨fppfFullInvariantIso f hL d b t, fppfFullInvariantIso_base f hL d b t⟩

include hc in
/-- The unchanged full parameter relation also has an actual effective scheme model. -/
theorem compatibleTranslation_exists_parameterIso :
    Nonempty (invariantLocallyRingedSpace (variableChartEquivalenceRelation f hL d W c) ≅
      (variableHilbertTest f d V).left.toLocallyRingedSpace) := by
  obtain ⟨t, ht, _⟩ := relativePicardFppf_singleton_existsUnique f b c hc
  subst c
  exact ⟨variableHilbertFppfQuotientIso f hL d b t⟩

include hc in
/-- Smooth compatible translations give actual open scheme neighborhoods of the old quotient. -/
theorem compatibleTranslation_exists_schemeNeighborhood [Smooth W.hom] :
    ∃ j : (variableHilbertTest f d V).left.toLocallyRingedSpace ⟶
        invariantLocallyRingedSpace (smoothHilbertEquivalenceRelation f hL),
      LocallyRingedSpace.IsOpenImmersion j ∧
        Set.range j.base = (smoothTranslationOrbitOpen f hL d W c :
          Set (Orbit (smoothHilbertEquivalenceRelation f hL))) ∧
        j ≫ invariantLocallyRingedBaseMap (smoothHilbertEquivalenceRelation f hL) =
          (variableHilbertTest f d V).hom.toLRSHom := by
  obtain ⟨t, ht, _⟩ := relativePicardFppf_singleton_existsUnique f b c hc
  subst c
  exact ⟨fppfFullSchemeNeighborhood f hL d b t, inferInstance,
    fppfFullSchemeNeighborhood_range f hL d b t, fppfFullSchemeNeighborhood_base f hL d b t⟩

end FLT.Mazur.OrderedHilbertBaseOpenChart
