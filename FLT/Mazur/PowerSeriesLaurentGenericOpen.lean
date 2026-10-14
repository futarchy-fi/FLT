/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import Mathlib.AlgebraicGeometry.Restrict
public import Mathlib.RingTheory.LaurentSeries

/-!
# The nonvanishing power-series parameter locus is a field spectrum

The Laurent series localization identifies the entire open scheme D(X),
not merely its points. Pulling this identification back gives the common
generic open of any scheme over the original power-series base.
-/

@[expose] public noncomputable section
open CategoryTheory Limits AlgebraicGeometry
namespace FLT.Mazur.PowerSeriesLaurentGenericOpen
set_option backward.isDefEq.respectTransparency false
variable (K : Type) [Field K]

/-- The actual inclusion of the Laurent series generic field. -/
abbrev genericInclusion : Spec (.of (LaurentSeries K)) ⟶ Spec (.of (PowerSeries K)) :=
  Spec.map (CommRingCat.ofHom (algebraMap (PowerSeries K) (LaurentSeries K)))

/-- Localization at the parameter agrees with the Laurent series field. -/
def localizationIso : Spec (.of (LaurentSeries K)) ≅
    Spec (.of (Localization.Away (PowerSeries.X : PowerSeries K))) :=
  let e := IsLocalization.algEquiv (.powers (PowerSeries.X : PowerSeries K))
    (Localization.Away (PowerSeries.X : PowerSeries K)) (LaurentSeries K)
  Scheme.Spec.mapIso e.toRingEquiv.toCommRingCatIso.op

/-- The localization comparison preserves the original coefficient inclusion. -/
@[reassoc] theorem localizationIso_inclusion :
    (localizationIso K).hom ≫ Spec.map (CommRingCat.ofHom
      (algebraMap (PowerSeries K) (Localization.Away (PowerSeries.X : PowerSeries K)))) =
        genericInclusion K := by
  change Spec.map (CommRingCat.ofHom (IsLocalization.algEquiv
    (.powers (PowerSeries.X : PowerSeries K))
      (Localization.Away (PowerSeries.X : PowerSeries K)) (LaurentSeries K)).toRingHom) ≫
        Spec.map _ = _
  rw [← Spec.map_comp, ← CommRingCat.ofHom_comp]
  congr 2
  apply RingHom.ext
  intro x
  exact (IsLocalization.algEquiv (.powers (PowerSeries.X : PowerSeries K))
    (Localization.Away (PowerSeries.X : PowerSeries K)) (LaurentSeries K)).commutes x

instance genericInclusion_isOpenImmersion : IsOpenImmersion (genericInclusion K) := by
  rw [← localizationIso_inclusion]
  infer_instance

/-- Its scheme-theoretic open image is exactly D(X). -/
theorem genericInclusion_opensRange : (genericInclusion K).opensRange =
    PrimeSpectrum.basicOpen (PowerSeries.X : PowerSeries K) := by
  apply TopologicalSpace.Opens.ext
  exact PrimeSpectrum.localization_away_comap_range (LaurentSeries K) PowerSeries.X

variable {X : Scheme} (f : X ⟶ Spec (.of (PowerSeries K)))

/-- The actual generic fiber is the entire original nonvanishing parameter open. -/
def fiberIso : pullback f (genericInclusion K) ≅
    (f ⁻¹ᵁ PrimeSpectrum.basicOpen (PowerSeries.X : PowerSeries K)).toScheme :=
  IsOpenImmersion.isoOfRangeEq (pullback.fst f (genericInclusion K))
    (Scheme.Opens.ι _) (by
      rw [IsOpenImmersion.range_pullbackFst, genericInclusion_opensRange,
        Scheme.Opens.range_ι])

/-- The forward comparison is over the unchanged original total space. -/
@[reassoc] theorem fiberIso_inclusion :
    (fiberIso K f).hom ≫ (f ⁻¹ᵁ PrimeSpectrum.basicOpen (PowerSeries.X : PowerSeries K)).ι =
      pullback.fst f (genericInclusion K) :=
  IsOpenImmersion.isoOfRangeEq_hom_fac _ _ _

/-- The inverse comparison is also over the unchanged original total space. -/
@[reassoc] theorem fiberIso_inv_fst :
    (fiberIso K f).inv ≫ pullback.fst f (genericInclusion K) =
      (f ⁻¹ᵁ PrimeSpectrum.basicOpen (PowerSeries.X : PowerSeries K)).ι :=
  IsOpenImmersion.isoOfRangeEq_inv_fac _ _ _

/-- The common generic open has its actual Laurent series structure morphism. -/
def toField : (f ⁻¹ᵁ PrimeSpectrum.basicOpen (PowerSeries.X : PowerSeries K)).toScheme ⟶
    Spec (.of (LaurentSeries K)) :=
  (fiberIso K f).inv ≫ pullback.snd f (genericInclusion K)

/-- This field structure makes the original open inclusion a Cartesian square. -/
theorem isPullback_toField : IsPullback
    (f ⁻¹ᵁ PrimeSpectrum.basicOpen (PowerSeries.X : PowerSeries K)).ι
    (toField K f) f (genericInclusion K) := by
  refine IsPullback.of_iso_pullback ⟨?_⟩ (fiberIso K f).symm
    (fiberIso_inv_fst K f) rfl
  rw [toField, Category.assoc, ← pullback.condition, ← Category.assoc, fiberIso_inv_fst]

/-- The parameter is nonzero in this actual generic field. -/
theorem parameter_ne_zero :
    algebraMap (PowerSeries K) (LaurentSeries K) PowerSeries.X ≠ 0 :=
  (IsLocalization.Away.algebraMap_isUnit (S := LaurentSeries K) PowerSeries.X).ne_zero

end FLT.Mazur.PowerSeriesLaurentGenericOpen
