/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.CyclicCharacteristicResidualPrincipalOpens

/-!
# Original chart maps to the actual invariant affine target

The normalized chart and its finite relabeling quotient have actual scheme
maps to the spectrum of the full residual invariant ring. Both retain the
entire same-chart relation. The normalized preimages of affine principal
opens are the saturated basic opens constructed from residual functions.
-/

@[expose] public noncomputable section
open CategoryTheory AlgebraicGeometry Opposite TopologicalSpace
namespace FLT.Mazur.CyclicCharacteristicOrbit
open CyclicCharacteristicAtlas
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
variable (n : ℕ) [NeZero n] (b : Bool)

/-- The original normalized chart maps as a scheme to the actual invariant affine target. -/
def chartAffineComparison : normalizedLocus n b ⟶
    invariantAffineTarget n (integerOpen n (chartInteger b)) :=
  ⟨chartToInvariantOpen n b ≫ invariantAffineComparison n (integerOpen n (chartInteger b))⟩

/-- The affine comparison retains all original same-chart comparison arrows. -/
@[reassoc] theorem chartAffineComparison_condition :
    productArrowSource n b b ≫ chartAffineComparison n b =
      productArrowTarget n b b ≫ chartAffineComparison n b := by
  apply Scheme.Hom.ext'
  change (productArrowSource n b b).toLRSHom ≫ chartToInvariantOpen n b ≫ _ =
    (productArrowTarget n b b).toLRSHom ≫ chartToInvariantOpen n b ≫ _
  rw [← Category.assoc, ← Category.assoc, chartToInvariantOpen_condition]

/-- The actual finite quotient therefore has a unique scheme map to the invariant spectrum. -/
theorem finiteAffineComparison_existsUnique :
    ∃! f : normalizedQuotient n b ⟶
      invariantAffineTarget n (integerOpen n (chartInteger b)),
      normalizedQuotientMap n b ≫ f = chartAffineComparison n b :=
  normalizedQuotientMap_existsUnique_desc n b (chartAffineComparison n b)
    (chartResidual_morphism_relabel n b _ (chartAffineComparison_condition n b))

/-- The finite quotient's actual scheme comparison with the full invariant affine target. -/
def finiteAffineComparison : normalizedQuotient n b ⟶
    invariantAffineTarget n (integerOpen n (chartInteger b)) :=
  (finiteAffineComparison_existsUnique n b).choose

/-- Its pullback is exactly the original normalized-chart affine comparison. -/
@[reassoc] theorem normalizedQuotientMap_finiteAffineComparison :
    normalizedQuotientMap n b ≫ finiteAffineComparison n b = chartAffineComparison n b :=
  (finiteAffineComparison_existsUnique n b).choose_spec.1

/-- The finite quotient comparison still coequalizes the full residual relation. -/
@[reassoc] theorem finiteAffineComparison_condition :
    (productArrowSource n b b ≫ normalizedQuotientMap n b) ≫ finiteAffineComparison n b =
      (productArrowTarget n b b ≫ normalizedQuotientMap n b) ≫ finiteAffineComparison n b := by
  simp only [Category.assoc, normalizedQuotientMap_finiteAffineComparison,
    chartAffineComparison_condition]

/-- Affine principal opens pull back to the exact saturated normalized residual basic opens. -/
theorem chartAffineComparison_preimage_basicOpen (s : chartResidualSections n b) :
    (chartAffineComparison n b).base ⁻¹'
        (PrimeSpectrum.basicOpen ((chartResidualSectionsEquiv n b).symm s)).carrier =
      ((normalizedLocus n b).basicOpen s.val : Set _) := by
  change (chartToInvariantOpen n b).base ⁻¹'
    ((invariantAffineComparison n (integerOpen n (chartInteger b))).base ⁻¹'
      (PrimeSpectrum.basicOpen ((chartResidualSectionsEquiv n b).symm s)).carrier) =
        ((normalizedLocus n b).basicOpen s.val : Set _)
  rw [invariantAffineComparison_preimage_basicOpen]
  exact congrArg SetLike.coe (residualPrincipal_chart_preimage n b s)

end FLT.Mazur.CyclicCharacteristicOrbit
