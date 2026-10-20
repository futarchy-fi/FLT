/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.CyclicCharacteristicFullAffineComparisonSpan

/-!
# Actual scheme graphs for the full residual overlap spans

Both overlap projections are open immersions, giving an isomorphism between
actual opens in the two residual spectra. Every original full comparison span
factors through this graph with both original residual projections retained.
-/

@[expose] public noncomputable section
open CategoryTheory Limits AlgebraicGeometry
namespace FLT.Mazur.CyclicCharacteristicOrbit
open CyclicCharacteristicAtlas
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
variable (n : ℕ) [NeZero n] (i j : InvariantAffineIndex n)

/-- The scheme overlap of any two full residual charts, also across characteristics. -/
def residualSchemeOverlap : Scheme :=
  pullback (affineResidualInclusion n i) (affineResidualInclusion n j)

/-- The left coordinate of the actual residual overlap. -/
def residualSchemeOverlapLeft : residualSchemeOverlap n i j ⟶ affineResidualSpectrum n i :=
  pullback.fst _ _

/-- The right coordinate of the actual residual overlap. -/
def residualSchemeOverlapRight : residualSchemeOverlap n i j ⟶ affineResidualSpectrum n j :=
  pullback.snd _ _

/-- The left overlap coordinate is an open immersion. -/
instance residualSchemeOverlapLeft_isOpenImmersion :
    IsOpenImmersion (residualSchemeOverlapLeft n i j) := by
  unfold residualSchemeOverlapLeft
  infer_instance

/-- The right overlap coordinate is an open immersion. -/
instance residualSchemeOverlapRight_isOpenImmersion :
    IsOpenImmersion (residualSchemeOverlapRight n i j) := by
  unfold residualSchemeOverlapRight
  infer_instance

/-- The overlap span is the graph of an actual isomorphism between open subschemes. -/
def residualOverlapGraphIso :
    (residualSchemeOverlapLeft n i j).opensRange.toScheme ≅
      (residualSchemeOverlapRight n i j).opensRange.toScheme :=
  (residualSchemeOverlapLeft n i j).isoOpensRange.symm ≪≫
    (residualSchemeOverlapRight n i j).isoOpensRange

/-- The graph isomorphism retains the original right projection from the overlap. -/
@[reassoc] theorem residualOverlapGraphIso_right :
    (residualSchemeOverlapLeft n i j).isoOpensRange.hom ≫
      (residualOverlapGraphIso n i j).hom ≫
        (residualSchemeOverlapRight n i j).opensRange.ι =
          residualSchemeOverlapRight n i j := by
  simp only [residualOverlapGraphIso, Iso.trans_hom, Iso.symm_hom,
    Category.assoc, Iso.hom_inv_id_assoc, Scheme.Hom.isoOpensRange_hom_ι]

/-- Every original full cross-chart comparison span maps to this actual scheme graph. -/
def fullAffineComparisonToOverlap : fullAffineComparisonSpan n i j ⟶ residualSchemeOverlap n i j :=
  pullback.lift (fullAffineComparisonSource n i j ≫ affineResidualProjection n i)
    (fullAffineComparisonTarget n i j ≫ affineResidualProjection n j)
    (fullAffineComparison_residual_condition n i j)

/-- Graph factorization retains the entire original residual source morphism. -/
@[reassoc] theorem fullAffineComparisonToOverlap_left :
    fullAffineComparisonToOverlap n i j ≫ residualSchemeOverlapLeft n i j =
      fullAffineComparisonSource n i j ≫ affineResidualProjection n i :=
  pullback.lift_fst _ _ _

/-- Graph factorization retains the entire original residual target morphism. -/
@[reassoc] theorem fullAffineComparisonToOverlap_right :
    fullAffineComparisonToOverlap n i j ≫ residualSchemeOverlapRight n i j =
      fullAffineComparisonTarget n i j ≫ affineResidualProjection n j :=
  pullback.lift_snd _ _ _

/-- The original residual source and target morphisms determine this graph factor uniquely. -/
theorem fullAffineComparisonToOverlap_unique
    (f : fullAffineComparisonSpan n i j ⟶ residualSchemeOverlap n i j)
    (hl : f ≫ residualSchemeOverlapLeft n i j =
      fullAffineComparisonSource n i j ≫ affineResidualProjection n i)
    (hr : f ≫ residualSchemeOverlapRight n i j =
      fullAffineComparisonTarget n i j ≫ affineResidualProjection n j) :
    f = fullAffineComparisonToOverlap n i j := by
  apply pullback.hom_ext
  · exact hl.trans (fullAffineComparisonToOverlap_left n i j).symm
  · exact hr.trans (fullAffineComparisonToOverlap_right n i j).symm

end FLT.Mazur.CyclicCharacteristicOrbit
