/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.HilbertIdentityGroundOriginalSection
public import FLT.Mazur.SmoothTranslationQuotientBaseSquare

/-!
# The identity-ground quotient retains the original coefficient morphism

The transported source base agrees with the base induced by both the original
chart quotient and its inclusion into the full original invariant quotient.
-/

@[expose] public noncomputable section
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry Opposite
namespace FLT.Mazur.HilbertChart.AffineRestriction
open CartierAbel SchemePicard FCurve RelativeRelationOrbit
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
variable {R : Type} [CommRing R] [Algebra.FiniteType ℤ R] {X : Scheme}
  (f : X ⟶ Spec (.of R)) [IsProper f] [Flat f] [GeometricallyIntegral f]
  [SmoothOfRelativeDimension 1 f] {L : X.Modules} (hL : AmpleLineBundle L)
  (d : ℕ) (V : Over (Spec (.of R))) [IsAffine V.left] [Etale V.hom]
  (c : (relativeFppfSheaf f).obj.obj (op V))
  {A : Over (Spec (.of R))} [IsAffine A.left] (k : A ⟶ variableHilbertTest f d V)
  [IsOpenImmersion k.left]

/-- The identity-ground quotient comparison preserves the original coefficient morphism. -/
@[reassoc]
theorem identityGroundOriginalQuotientMap_baseMap :
    identityGroundOriginalQuotientMap f hL d V c k ≫
        invariantLocallyRingedBaseMap (variableChartEquivalenceRelation f hL d V c) =
      (identityGroundOriginalTest f hL d V c k).hom.toLRSHom := by
  rw [identityGroundOriginalQuotientMap_eq, Category.assoc, Category.assoc,
    invariantLocallyRingedProjection_baseMap, ← Scheme.Hom.comp_toLRSHom, k.w]
  rfl

/-- The map into the full ORIGINAL quotient has exactly the transported original base. -/
@[reassoc]
theorem identityGroundOriginalQuotientMap_globalBase :
    identityGroundOriginalQuotientMap f hL d V c k ≫
        smoothTranslationQuotientInclusion f hL d V c ≫
        invariantLocallyRingedBaseMap (smoothHilbertEquivalenceRelation f hL) =
      (identityGroundOriginalTest f hL d V c k).hom.toLRSHom := by
  rw [smoothTranslationQuotientInclusion_baseMap,
    identityGroundOriginalQuotientMap_baseMap]

end FLT.Mazur.HilbertChart.AffineRestriction
