/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.OrderedHilbertChartFullEquivalence
public import FLT.Mazur.OrderedHilbertChartQuotientComparison
public import FLT.Mazur.SmoothTranslationQuotientBaseSquare

/-!
# Full original chart invariants as actual open quotient neighborhoods

For every smooth translation base, the complete invariant locally ringed
quotient of the constructed source restriction embeds openly into the old
original quotient. This compares all regular functions and coefficient maps;
it does not assume or conclude that the neighborhood is a scheme.
-/

@[expose] public noncomputable section
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry Opposite
namespace FLT.Mazur.OrderedHilbertBaseOpenChart
open HilbertChart CartierAbel SchemePicard FCurve RelativeRelationOrbit
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
variable {R : Type} [CommRing R] [Algebra.FiniteType ℤ R]
  {X : Scheme} (f : X ⟶ Spec (.of R)) [IsProper f] [Flat f] [GeometricallyIntegral f]
  [SmoothOfRelativeDimension 1 f] {L : X.Modules} (hL : AmpleLineBundle L)
  (d : ℕ) (V : Over (Spec (.of R)))
  (c : (relativeFppfSheaf f).obj.obj (op V))
local notation "e₁" => fullRestrictedEquivalence f hL d V c
local notation "e₂" => variableChartEquivalenceRelation f hL d V c
local notation "e₀" => smoothHilbertEquivalenceRelation f hL

/-- The full original restriction and full parameter relation have identical invariant sheaves. -/
def fullInvariantComparisonIso :
    invariantLocallyRingedSpace e₁ ≅ invariantLocallyRingedSpace e₂ :=
  (invariantLocallyRingedIso e₁).symm ≪≫ fullChartInvariantIso f hL d V c

/-- The invariant comparison retains the actual geometric projection. -/
@[reassoc]
theorem fullInvariantComparisonIso_source :
    invariantLocallyRingedProjection e₁ ≫ (fullInvariantComparisonIso f hL d V c).hom =
      (projection f hL d V c).left.toLRSHom ≫ invariantLocallyRingedProjection e₂ := by
  dsimp only [invariantLocallyRingedProjection, fullInvariantComparisonIso,
    Iso.trans_hom, Iso.symm_hom]
  rw [Category.assoc, Iso.hom_inv_id_assoc]
  exact fullChartInvariantIso_source f hL d V c

/-- The invariant comparison preserves the original coefficient base. -/
theorem fullInvariantComparisonIso_base :
    (fullInvariantComparisonIso f hL d V c).hom ≫ invariantLocallyRingedBaseMap e₂ =
      invariantLocallyRingedBaseMap e₁ := by
  dsimp only [fullInvariantComparisonIso, Iso.trans_hom, Iso.symm_hom]
  rw [Category.assoc, fullChartInvariantIso_base]
  rfl

variable [Smooth V.hom]

/-- The entire original restricted quotient maps into the OLD original quotient. -/
def fullOriginalQuotientInclusion :
    invariantLocallyRingedSpace e₁ ⟶ invariantLocallyRingedSpace e₀ :=
  (fullInvariantComparisonIso f hL d V c).hom ≫
    smoothTranslationQuotientInclusion f hL d V c

/-- This is an actual open immersion of locally ringed spaces, not merely an open point map. -/
instance fullOriginalQuotientInclusion_isOpenImmersion :
    LocallyRingedSpace.IsOpenImmersion (fullOriginalQuotientInclusion f hL d V c) := by
  dsimp only [fullOriginalQuotientInclusion]
  infer_instance

/-- The full original-source projection is preserved by the old quotient inclusion. -/
@[reassoc]
theorem fullOriginalQuotientInclusion_source :
    invariantLocallyRingedProjection e₁ ≫ fullOriginalQuotientInclusion f hL d V c =
      (projection f hL d V c).left.toLRSHom ≫ invariantLocallyRingedProjection e₂ ≫
        smoothTranslationQuotientInclusion f hL d V c := by
  dsimp only [fullOriginalQuotientInclusion]
  rw [fullInvariantComparisonIso_source_assoc]

/-- The original coefficient map survives the full open-neighborhood comparison. -/
theorem fullOriginalQuotientInclusion_base :
    fullOriginalQuotientInclusion f hL d V c ≫ invariantLocallyRingedBaseMap e₀ =
      invariantLocallyRingedBaseMap e₁ := by
  dsimp only [fullOriginalQuotientInclusion]
  rw [Category.assoc, smoothTranslationQuotientInclusion_baseMap,
    fullInvariantComparisonIso_base]

/-- No original quotient point is lost in passing to the full restricted presentation. -/
theorem fullOriginalQuotientInclusion_range :
    Set.range (fullOriginalQuotientInclusion f hL d V c).base =
      (smoothTranslationOrbitOpen f hL d V c : Set (Orbit e₀)) := by
  have hs := (TopCat.homeoOfIso
    (LocallyRingedSpace.forgetToTop.mapIso (fullInvariantComparisonIso f hL d V c))).surjective
  change Function.Surjective (fullInvariantComparisonIso f hL d V c).hom.base at hs
  change Set.range ((smoothTranslationQuotientInclusion f hL d V c).base ∘
    (fullInvariantComparisonIso f hL d V c).hom.base) = _
  rw [Set.range_comp, hs.range_eq]
  simpa only [Set.image_univ] using smoothTranslationQuotientInclusion_range f hL d V c

end FLT.Mazur.OrderedHilbertBaseOpenChart
