/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.PowerSeriesLaurentGenericOpen

/-!
# The actual fraction-field generic fiber is the parameter open

The fraction-field comparison is over the original power-series ring. Hence
its inclusion has the same entire open image as the Laurent-series inclusion.
-/

@[expose] public noncomputable section
open CategoryTheory Limits AlgebraicGeometry
namespace FLT.Mazur.PowerSeriesFractionGenericOpen
set_option backward.isDefEq.respectTransparency false
variable (K : Type) [Field K]
local notation "F" => FractionRing (PowerSeries K)

/-- The actual fraction-field coefficient inclusion. -/
abbrev genericInclusion : Spec (.of (F)) ⟶ Spec (.of (PowerSeries K)) :=
  Spec.map (CommRingCat.ofHom (algebraMap (PowerSeries K) (F)))

/-- Both fraction-field models are compared over the unchanged power-series coefficients. -/
def laurentIso : Spec (.of (F)) ≅ Spec (.of (LaurentSeries K)) :=
  Scheme.Spec.mapIso (IsLocalization.algEquiv (nonZeroDivisors (PowerSeries K))
    (LaurentSeries K) (F)).toRingEquiv.toCommRingCatIso.op

/-- The comparison preserves the actual original generic inclusion. -/
@[reassoc] theorem laurentIso_inclusion :
    (laurentIso K).hom ≫ PowerSeriesLaurentGenericOpen.genericInclusion K =
      genericInclusion K := by
  change Spec.map (CommRingCat.ofHom (IsLocalization.algEquiv
    (nonZeroDivisors (PowerSeries K)) (LaurentSeries K) (F)).toRingHom) ≫ Spec.map _ = _
  rw [← Spec.map_comp, ← CommRingCat.ofHom_comp]
  congr 2
  apply RingHom.ext
  exact (IsLocalization.algEquiv (nonZeroDivisors (PowerSeries K))
    (LaurentSeries K) (F)).commutes

instance genericInclusion_isOpenImmersion : IsOpenImmersion (genericInclusion K) := by
  rw [← laurentIso_inclusion]
  infer_instance

/-- The image is precisely the nonvanishing locus of the original parameter. -/
theorem genericInclusion_opensRange : (genericInclusion K).opensRange =
    PrimeSpectrum.basicOpen (PowerSeries.X : PowerSeries K) := by
  let _ : IsLocalization.Away (PowerSeries.X : PowerSeries K) (F) :=
    IsLocalization.isLocalization_of_algEquiv _
      (IsLocalization.algEquiv (nonZeroDivisors (PowerSeries K)) (LaurentSeries K) (F))
  apply TopologicalSpace.Opens.ext
  exact PrimeSpectrum.localization_away_comap_range (F) PowerSeries.X

variable {X : Scheme} (s : X ⟶ Spec (.of (PowerSeries K)))

/-- The full actual generic fiber is the entire original parameter open. -/
def fiberIso : pullback s (genericInclusion K) ≅
    (s ⁻¹ᵁ PrimeSpectrum.basicOpen (PowerSeries.X : PowerSeries K)).toScheme :=
  IsOpenImmersion.isoOfRangeEq (pullback.fst s (genericInclusion K))
    (Scheme.Opens.ι _) (by
      rw [IsOpenImmersion.range_pullbackFst, genericInclusion_opensRange,
        Scheme.Opens.range_ι])

/-- The generic-open isomorphism retains the original total-space inclusion. -/
@[reassoc] theorem fiberIso_inclusion :
    (fiberIso K s).hom ≫ (s ⁻¹ᵁ PrimeSpectrum.basicOpen (PowerSeries.X : PowerSeries K)).ι =
      pullback.fst s (genericInclusion K) :=
  IsOpenImmersion.isoOfRangeEq_hom_fac _ _ _

end FLT.Mazur.PowerSeriesFractionGenericOpen
