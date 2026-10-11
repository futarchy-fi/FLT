/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.PolygonCompleteClosedFiber
public import FLT.Mazur.PolygonOriginalAdicRealization
public import FLT.Mazur.PolygonClosedScalarLifting
public import FLT.Mazur.AffineSpectrumKernelIdeal
public import FLT.Mazur.WeierstrassSpecSections

/-!
# The original closed polygon is the complete parameter subscheme

The cartesian closed-fiber square identifies its actual defining ideal.
The same original coefficient maps lift all closed functions as constants.
-/

@[expose] public noncomputable section

open CategoryTheory AlgebraicGeometry

namespace FLT.Mazur.PolygonInfinitesimalStages

open FCurve BaseAdicThickening Scheme.IdealSheafData WeierstrassIntegralChart

set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true

attribute [local irreducible] exactVeroneseProj exactVeroneseProjToBase
  originalStageToCompatibleProj

/-- Closed restriction surjectivity is preserved by a specified isomorphism of its source. -/
theorem closedRestriction_appTop_surjective_of_iso {X Y Z : Scheme}
    (e : Y ≅ Z) (i : Z ⟶ X) (f : Y ⟶ X) (he : e.hom ≫ i = f)
    (hf : Function.Surjective f.appTop) : Function.Surjective i.appTop := by
  intro s
  obtain ⟨t, ht⟩ := hf (e.hom.appTop s)
  refine ⟨t, (ConcreteCategory.bijective_of_isIso e.hom.appTop).injective ?_⟩
  rw [← he, Scheme.Hom.comp_appTop] at ht
  exact ht

variable (K : Type) [Field K] (n : ℕ) (h : 2 ≤ n) [NeZero n]

/-- The original closed coefficient point is a closed immersion. -/
instance completeClosedBase_isClosedImmersion : IsClosedImmersion (completeClosedBase K) :=
  IsClosedImmersion.spec_of_surjective _ (fun a ↦ ⟨PowerSeries.C a, by simp⟩)

/-- The original complete closed-fiber inclusion is a closed immersion. -/
instance completeClosedFiberInclusion_isClosedImmersion :
    IsClosedImmersion (completeClosedFiberInclusion K n h) :=
  MorphismProperty.of_isPullback (completeClosedFiber_isPullback K n h).flip inferInstance

/-- The closed coefficient point is defined by the actual power-series parameter. -/
theorem completeClosedBase_ker : (completeClosedBase K).ker =
    baseIdeal (.of (PowerSeries K)) (parameterIdeal K) := by
  rw [completeClosedBase, specMap_ker_baseIdeal]
  congr 1
  ext f
  exact (PowerSeries.X_dvd_iff).symm.trans (Ideal.mem_span_singleton).symm

/-- The actual closed polygon has the original extended parameter ideal as its kernel. -/
theorem completeClosedFiberInclusion_ker :
    (completeClosedFiberInclusion K n h).ker = compatibleProjAdicIdeal K n h := by
  rw [← completeClosedFiberIso_fst K n h, Scheme.Hom.ker_comp_of_isIso,
    ker_fst_of_isClosedImmersion, completeClosedBase_ker]
  rfl

/-- The original closed polygon is the actual complete parameter subscheme. -/
def completeClosedIdealIso : PolygonCyclicAtlas.scheme K n h ≅
    (compatibleProjAdicIdeal K n h).subscheme :=
  asIso (completeClosedFiberInclusion K n h).toImage ≪≫
    subschemeCongr (completeClosedFiberInclusion_ker K n h)

/-- The closed-ideal comparison preserves the original polygon inclusion. -/
@[reassoc] theorem completeClosedIdealIso_hom_ι :
    (completeClosedIdealIso K n h).hom ≫ (compatibleProjAdicIdeal K n h).subschemeι =
      completeClosedFiberInclusion K n h := by
  rw [completeClosedIdealIso, Iso.trans_hom, Category.assoc, subschemeCongr_hom_ι]
  exact Scheme.Hom.toImage_imageι _

/-- Original complete coefficients restrict through their actual constant coefficient. -/
theorem completeClosedFiber_scalar (a : PowerSeries K) :
    (completeClosedFiberInclusion K n h).appTop
        (specSectionHom (exactVeroneseProjToBase K n h) a) =
      structureScalarMap (PolygonCyclicAtlas.toBase K n h) (PowerSeries.constantCoeff a) := by
  have he := congrArg specSectionHom (completeClosedFiber_isPullback K n h).w
  rw [completeClosedBase, specSectionHom_comp] at he
  exact DFunLike.congr_fun he a

/-- Closed global functions lift through the actual complete inclusion as constants. -/
theorem completeClosedFiber_appTop_surjective :
    Function.Surjective (completeClosedFiberInclusion K n h).appTop := by
  intro s
  obtain ⟨a, ha⟩ := (closedPolygon_constantSections K n h).2 s
  refine ⟨specSectionHom (exactVeroneseProjToBase K n h) (PowerSeries.C a), ?_⟩
  rw [completeClosedFiber_scalar, PowerSeries.constantCoeff_C]
  exact ha

/-- The same lifting statement holds on the actual principal closed subscheme. -/
theorem completeClosedIdeal_appTop_surjective :
    Function.Surjective (compatibleProjAdicIdeal K n h).subschemeι.appTop :=
  closedRestriction_appTop_surjective_of_iso (completeClosedIdealIso K n h) _ _
    (completeClosedIdealIso_hom_ι K n h) (completeClosedFiber_appTop_surjective K n h)

end FLT.Mazur.PolygonInfinitesimalStages
