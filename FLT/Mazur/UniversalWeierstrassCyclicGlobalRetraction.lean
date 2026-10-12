/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.UniversalWeierstrassCyclicFullNaturality
public import FLT.Mazur.UniversalWeierstrassCyclicSliceRetraction

/-!
# The actual global full normalization retracts its closed slice

Full sourcewise coherence transfers the already proved slice retraction to the
global morphism. The resulting idempotence concerns the actual complete cyclic
parameter scheme; it does not assert that this slice is a modular quotient.
-/

@[expose] public noncomputable section
open CategoryTheory AlgebraicGeometry
namespace FLT.Mazur.UniversalWeierstrass
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
variable (n : ℕ) [NeZero n]

/-- The global full normalization is a retraction onto the original closed full slice. -/
@[reassoc] theorem cyclicNormalizationSliceMap_retraction :
    cyclicNormalizedSliceInclusion n ≫ cyclicNormalizationSliceMap n = 𝟙 _ := by
  change cyclicNaturalNormalizedSlicePoint n (cyclicNormalizedSliceInclusion n) = _
  rw [← cyclicSchemeNormalizedSlicePoint_eq_natural]
  simpa only [Category.id_comp] using cyclicSchemeNormalizedSlicePoint_restrict n (𝟙 _)

/-- The actual global normalization fixes the full closed-slice inclusion. -/
@[reassoc] theorem cyclicNormalizationMap_restrict :
    cyclicNormalizedSliceInclusion n ≫ cyclicNormalizationMap n =
      cyclicNormalizedSliceInclusion n := by
  rw [← cyclicNormalizationSliceMap_inclusion, cyclicNormalizationSliceMap_retraction_assoc]

/-- The actual global complete cyclic normalization morphism is idempotent. -/
@[reassoc] theorem cyclicNormalizationMap_idempotent :
    cyclicNormalizationMap n ≫ cyclicNormalizationMap n = cyclicNormalizationMap n := by
  have h := cyclicSchemeNormalizedPoint_idempotent n (𝟙 _)
  rw [cyclicSchemeNormalizedPoint_eq_comp n (cyclicSchemeNormalizedPoint n (𝟙 _))] at h
  exact h

/-- The full closed-slice parameter is unchanged by the actual global normalization. -/
@[reassoc] theorem cyclicNormalizationSliceMap_idempotent :
    cyclicNormalizationMap n ≫ cyclicNormalizationSliceMap n =
      cyclicNormalizationSliceMap n := by
  rw [← cyclicNormalizationSliceMap_inclusion, Category.assoc,
    cyclicNormalizationSliceMap_retraction, Category.comp_id]

end FLT.Mazur.UniversalWeierstrass
