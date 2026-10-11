/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.SmoothTranslationSectionRestriction

/-!
# Naturality of the actual invariant section comparison

The original-to-chart ring equivalences commute with all restrictions on the
quotient neighborhood. Consequently their inverses commute with restriction too.
-/

@[expose] public noncomputable section
open CategoryTheory AlgebraicGeometry Opposite
namespace FLT.Mazur.HilbertChart
open CartierAbel SchemePicard FCurve SchemeEffectiveEpiSections RelativeRelationOrbit
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
variable {R : Type} [CommRing R] [Algebra.FiniteType ℤ R]
  {X : Scheme} (f : X ⟶ Spec (.of R)) [IsProper f] [Flat f] [GeometricallyIntegral f]
  [SmoothOfRelativeDimension 1 f] {L : X.Modules} (hL : AmpleLineBundle L)
  (d : ℕ) (V : Over (Spec (.of R))) [Smooth V.hom]
  (c : (relativeFppfSheaf f).obj.obj (op V))
  {O P : TopologicalSpace.Opens (Orbit (smoothHilbertEquivalenceRelation f hL))}

/-- The actual invariant-sheaf section comparison is natural in every open inclusion. -/
theorem smoothTranslationInvariantSectionRingEquiv_natural (h : O ≤ P)
    (hP : P ≤ smoothTranslationOrbitOpen f hL d V c)
    (s : (invariantSheaf (smoothHilbertEquivalenceRelation f hL)).obj.obj (op P)) :
    smoothTranslationInvariantSectionRingEquiv f hL d V c O (h.trans hP)
      ((invariantSheaf (smoothHilbertEquivalenceRelation f hL)).obj.map
        (homOfLE h).op s) =
      (invariantSheaf (variableChartEquivalenceRelation f hL d V c)).obj.map
        (homOfLE (smoothTranslationFullChartOrbitOpen_mono f hL d V c h)).op
        (smoothTranslationInvariantSectionRingEquiv f hL d V c P hP s) := by
  apply (smoothTranslationChartSectionEquiv f hL d V c O).injective
  apply Subtype.ext
  rw [smoothTranslationInvariantSectionRingEquiv_common]
  rw [smoothTranslationOriginalSectionEquiv_restrict f hL d V c h hP,
    smoothTranslationChartSectionEquiv_restrict f hL d V c h,
    smoothTranslationInvariantSectionRingEquiv_common]

/-- The inverse comparison also preserves every restriction of chart invariant sections. -/
theorem smoothTranslationInvariantSectionRingEquiv_symm_natural (h : O ≤ P)
    (hP : P ≤ smoothTranslationOrbitOpen f hL d V c)
    (s : (invariantSheaf (variableChartEquivalenceRelation f hL d V c)).obj.obj
      (op (smoothTranslationFullChartOrbitOpen f hL d V c P))) :
    (smoothTranslationInvariantSectionRingEquiv f hL d V c O (h.trans hP)).symm
      ((invariantSheaf (variableChartEquivalenceRelation f hL d V c)).obj.map
        (homOfLE (smoothTranslationFullChartOrbitOpen_mono f hL d V c h)).op s) =
      (invariantSheaf (smoothHilbertEquivalenceRelation f hL)).obj.map (homOfLE h).op
        ((smoothTranslationInvariantSectionRingEquiv f hL d V c P hP).symm s) := by
  apply (smoothTranslationInvariantSectionRingEquiv f hL d V c O (h.trans hP)).injective
  rw [RingEquiv.apply_symm_apply,
    smoothTranslationInvariantSectionRingEquiv_natural f hL d V c h hP,
    RingEquiv.apply_symm_apply]

end FLT.Mazur.HilbertChart
