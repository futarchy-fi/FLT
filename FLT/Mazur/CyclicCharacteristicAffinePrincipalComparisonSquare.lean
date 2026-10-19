/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.CyclicCharacteristicAffineResidualPrincipalSpectrum

/-!
# Compatibility of principal spectra with the original affine comparison

The localized residual map and the original invariant restriction give the
same scheme morphism after the original section-ring comparison. Thus the
basic-open identifications retain the original quotient sheaf restriction.
-/

@[expose] public noncomputable section
open CategoryTheory AlgebraicGeometry
namespace FLT.Mazur.CyclicCharacteristicOrbit
open CyclicCharacteristicAtlas
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
variable (n : ℕ) [NeZero n] (i : InvariantAffineIndex n) (s : affineResidualSections n i)

/-- The localized full residual comparison commutes with the original invariant restriction. -/
@[reassoc] theorem affineResidualPrincipalSpectrumMap_comparison :
    affineResidualPrincipalSpectrumMap n i s ≫ affineResidualComparison n i =
      invariantAffinePrincipalMap n (affineOrbitOpen n i)
        ((affineResidualSectionsEquiv n i).symm s) := by
  unfold affineResidualPrincipalSpectrumMap affineResidualComparison invariantAffinePrincipalMap
  rw [← Spec.map_comp]
  apply congrArg Spec.map
  ext a
  exact affineResidualPrincipalRestriction_section n i s a

/-- The actual principal open embedding retains the original section-spectrum restriction. -/
@[reassoc] theorem affineResidualPrincipalSpectrumIso_comparison :
    (affineResidualPrincipalSpectrumIso n i s).hom ≫
      (affineResidualSpectrumBasicOpen n i s).ι ≫ affineResidualComparison n i =
      invariantAffinePrincipalMap n (affineOrbitOpen n i)
        ((affineResidualSectionsEquiv n i).symm s) := by
  rw [← Category.assoc, affineResidualPrincipalSpectrumIso_inclusion,
    affineResidualPrincipalSpectrumMap_comparison]

end FLT.Mazur.CyclicCharacteristicOrbit
