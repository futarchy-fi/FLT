/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.AuxiliaryLevelFiniteNeighborhood
public import FLT.Mazur.CyclicCharacteristicLocusSeparated
public import FLT.Mazur.ProjectiveFiniteAffineNeighborhood

/-!
# Finite affine neighborhoods on the actual characteristic loci

The original cubic's closed projective embedding supplies the neighborhoods.
Pass through finite marking powers, faithful opens, products and closed subgroup
loci. No ampleness or neighborhood conclusion is assumed for the parameter spaces.
-/

@[expose] public noncomputable section
open CategoryTheory AlgebraicGeometry
namespace FLT.Mazur.CyclicCharacteristicAtlas
open FiniteAffineNeighborhood
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

/-- The original projective cubic has common affine neighborhoods of all finite sets. -/
theorem integralCurve_hasFiniteNeighborhoods {R : Type} [CommRing R] (W : WeierstrassCurve R) :
    HasNeighborhoods (WeierstrassIntegralChart.integralCurve W) := by
  intro s hs
  obtain ⟨U, hU⟩ := ProjectiveSpace.exists_affineOpen_of_closed_embedding
    (WeierstrassIntegralChart.integralProjectiveMap W) s hs
  exact ⟨U.val, U.property, hU⟩

/-- Common affine neighborhoods on the original even universal group. -/
theorem evenGroup_hasFiniteNeighborhoods :
    HasNeighborhoods UniversalWeierstrass.universalGroup.left :=
  integralCurve_hasFiniteNeighborhoods UniversalWeierstrass.smoothEquation

/-- Common affine neighborhoods on the original odd universal group. -/
theorem oddGroup_hasFiniteNeighborhoods :
    HasNeighborhoods OddWeierstrassParameter.universalGroup.left :=
  integralCurve_hasFiniteNeighborhoods IntegralWeierstrassParameter.oddChartEquation

/-- The original even coefficient spectrum is affine. -/
instance evenCoefficient_isAffine : IsAffine UniversalWeierstrass.parameterBase := by
  change IsAffine (Spec (.of UniversalWeierstrass.ParameterRing))
  infer_instance

/-- The original odd coefficient spectrum is affine. -/
instance oddCoefficient_isAffine : IsAffine OddWeierstrassParameter.parameterBase := by
  change IsAffine (Spec (.of IntegralWeierstrassParameter.OddChartRing))
  infer_instance

variable (n : ℕ) [NeZero n]

/-- The full even parameter scheme has common affine neighborhoods. -/
theorem evenParameter_hasFiniteNeighborhoods :
    HasNeighborhoods (UniversalWeierstrass.cyclicHomAuxiliaryScheme n).left :=
  overProd _ _ (faithfulScheme _ _ evenGroup_hasFiniteNeighborhoods)
    (homScheme _ _ evenGroup_hasFiniteNeighborhoods)

/-- The full odd parameter scheme has common affine neighborhoods. -/
theorem oddParameter_hasFiniteNeighborhoods :
    HasNeighborhoods (OddWeierstrassParameter.cyclicHomAuxiliaryScheme n).left :=
  overProd _ _ (faithfulScheme _ _ oddGroup_hasFiniteNeighborhoods)
    (homScheme _ _ oddGroup_hasFiniteNeighborhoods)

/-- The actual even subgroup locus has common affine neighborhoods. -/
theorem evenLocus_hasFiniteNeighborhoods :
    HasNeighborhoods (UniversalWeierstrass.cyclicHomUniversalMultiplicationLocus n) :=
  of_affineHom (UniversalWeierstrass.cyclicHomUniversalMultiplicationLocusInclusion n)
    (evenParameter_hasFiniteNeighborhoods n)

/-- The actual odd subgroup locus has common affine neighborhoods. -/
theorem oddLocus_hasFiniteNeighborhoods :
    HasNeighborhoods (OddWeierstrassParameter.cyclicHomUniversalMultiplicationLocus n) :=
  of_affineHom (OddWeierstrassParameter.cyclicHomUniversalMultiplicationLocusInclusion n)
    (oddParameter_hasFiniteNeighborhoods n)

/-- The actual even normalized subgroup locus has common affine neighborhoods. -/
theorem evenNormalizedLocus_hasFiniteNeighborhoods :
    HasNeighborhoods (UniversalWeierstrass.cyclicHomNormalizedLocus n) :=
  of_affineHom (UniversalWeierstrass.cyclicHomNormalizedLocusInclusion n)
    (evenLocus_hasFiniteNeighborhoods n)

/-- The actual odd normalized subgroup locus has common affine neighborhoods. -/
theorem oddNormalizedLocus_hasFiniteNeighborhoods :
    HasNeighborhoods (OddWeierstrassParameter.cyclicHomNormalizedLocus n) :=
  of_affineHom (OddWeierstrassParameter.cyclicHomNormalizedLocusInclusion n)
    (oddLocus_hasFiniteNeighborhoods n)

end FLT.Mazur.CyclicCharacteristicAtlas
