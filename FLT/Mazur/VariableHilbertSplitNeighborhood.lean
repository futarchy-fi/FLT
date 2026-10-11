/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.VariableHilbertSplitQuotient
public import FLT.Mazur.SmoothTranslationQuotientOpenImmersion

/-!
# Actual scheme neighborhoods in the original quotient from split translations

The effective full chart quotient embeds openly in the original invariant
quotient. Its image is exactly the original smooth-translation open, including
all translation-base coordinates. Coverage of all quotient points is separate.
-/

@[expose] public noncomputable section
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry Opposite
namespace FLT.Mazur.HilbertChart
open CartierAbel SchemePicard FCurve RelativeRelationOrbit
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
variable {R : Type} [CommRing R] {X : Scheme} (f : X ⟶ Spec (.of R))
  [Algebra.FiniteType ℤ R] [IsProper f] [Flat f] [GeometricallyIntegral f]
  [SmoothOfRelativeDimension 1 f] {L : X.Modules} (hL : AmpleLineBundle L)
  (d : ℕ) {V W : Over (Spec (.of R))} (b : W ⟶ V)
  [IsOpenImmersion V.hom] [Smooth W.hom]
  (c : (relativeFppfSheaf f).obj.obj (op V)) (s : V ⟶ W) (hs : s ≫ b = 𝟙 V)
local notation "cW" => CategoryTheory.Functor.map
  (ObjectProperty.FullSubcategory.obj (relativeFppfSheaf f)) (Quiver.Hom.op b) c

/-- An actual scheme maps openly to the original full invariant Picard quotient. -/
def variableHilbertSplitNeighborhood :
    (variableHilbertTest f d V).left.toLocallyRingedSpace ⟶
      invariantLocallyRingedSpace (smoothHilbertEquivalenceRelation f hL) :=
  (variableHilbertSplitQuotientIso f hL d b c s hs).inv ≫
    smoothTranslationQuotientInclusion f hL d W cW

instance variableHilbertSplitNeighborhood_isOpenImmersion :
    LocallyRingedSpace.IsOpenImmersion (variableHilbertSplitNeighborhood f hL d b c s hs) := by
  unfold variableHilbertSplitNeighborhood
  infer_instance

/-- The actual source parameters map to the original full quotient through this scheme. -/
theorem variableHilbertSplitNeighborhood_source :
    (baseMarkedChartChange f b d).left.toLRSHom ≫
      variableHilbertSplitNeighborhood f hL d b c s hs =
        invariantLocallyRingedProjection (variableChartEquivalenceRelation f hL d W cW) ≫
          smoothTranslationQuotientInclusion f hL d W cW := by
  rw [← variableHilbertSplitQuotientIso_projection f hL d b c s hs]
  simp only [variableHilbertSplitNeighborhood, Category.assoc, Iso.hom_inv_id_assoc]

/-- This scheme covers the entire ORIGINAL full chart quotient image. -/
theorem variableHilbertSplitNeighborhood_range :
    Set.range (variableHilbertSplitNeighborhood f hL d b c s hs).base =
      (smoothTranslationOrbitOpen f hL d W cW :
        Set (Orbit (smoothHilbertEquivalenceRelation f hL))) := by
  rw [← smoothTranslationQuotientInclusion_range f hL d W cW]
  have hsur : Function.Surjective
      (variableHilbertSplitQuotientIso f hL d b c s hs).inv.base :=
    (TopCat.homeoOfIso (LocallyRingedSpace.forgetToTop.mapIso
      (variableHilbertSplitQuotientIso f hL d b c s hs).symm)).surjective
  ext z
  constructor
  · rintro ⟨x, rfl⟩
    exact ⟨(variableHilbertSplitQuotientIso f hL d b c s hs).inv.base x, rfl⟩
  · rintro ⟨x, rfl⟩
    obtain ⟨y, rfl⟩ := hsur x
    exact ⟨y, rfl⟩

/-- Every point of that full original quotient open has a point on the constructed scheme. -/
theorem variableHilbertSplitNeighborhood_covers
    (z : Orbit (smoothHilbertEquivalenceRelation f hL))
    (hz : z ∈ smoothTranslationOrbitOpen f hL d W cW) :
    ∃ x, (variableHilbertSplitNeighborhood f hL d b c s hs).base x = z := by
  exact (Set.ext_iff.mp (variableHilbertSplitNeighborhood_range f hL d b c s hs) z).mpr hz

include hs in
/-- Every point of the full split chart image has an actual affine neighborhood in the quotient. -/
theorem variableHilbertSplitNeighborhood_affine
    (z : Orbit (smoothHilbertEquivalenceRelation f hL))
    (hz : z ∈ smoothTranslationOrbitOpen f hL d W cW) :
    ∃ (A : CommRingCat) (j : (Spec A).toLocallyRingedSpace ⟶
        invariantLocallyRingedSpace (smoothHilbertEquivalenceRelation f hL)),
      LocallyRingedSpace.IsOpenImmersion j ∧ z ∈ Set.range j.base ∧
        Set.range j.base ⊆ (smoothTranslationOrbitOpen f hL d W cW :
          Set (Orbit (smoothHilbertEquivalenceRelation f hL))) := by
  obtain ⟨x, hx⟩ := variableHilbertSplitNeighborhood_covers f hL d b c s hs z hz
  obtain ⟨A, a, ha, y, hy⟩ := (variableHilbertTest f d V).left.exists_Spec_apply_eq x
  refine ⟨A, a.toLRSHom ≫ variableHilbertSplitNeighborhood f hL d b c s hs,
    inferInstance, ⟨y, ?_⟩, ?_⟩
  · change (variableHilbertSplitNeighborhood f hL d b c s hs).base (a y) = z
    exact (congrArg (variableHilbertSplitNeighborhood f hL d b c s hs).base hy).trans hx
  · rintro _ ⟨w, rfl⟩
    apply (Set.ext_iff.mp (variableHilbertSplitNeighborhood_range f hL d b c s hs) _).mp
    exact ⟨a w, rfl⟩

end FLT.Mazur.HilbertChart
