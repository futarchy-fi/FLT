/-
Copyright (c) 2026 krandder. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: krandder
-/
module

public import FLT.Mazur.AffineSpectrumKernelIdeal
public import FLT.Mazur.PolygonArithmeticRestrictionKernel
public import FLT.Mazur.PolygonArithmeticStageRestriction

/-!
# The original arithmetic stages are actual adic closed subschemes

The adjacent arithmetic transition is a surjective closed immersion with
exactly the last power of the original parameter ideal as its kernel. The
resulting ideal-subscheme comparison retains that original transition map.
-/

@[expose] public noncomputable section
open CategoryTheory Limits AlgebraicGeometry
namespace FLT.Mazur.PolygonArithmeticStages
open FCurve BaseAdicThickening Scheme.IdealSheafData
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
variable (A : Type*) [CommRing A] (π : A) (m : ℕ)

/-- Adjacent arithmetic coefficient restriction is a closed immersion on spectra. -/
instance baseRestriction_isClosedImmersion : IsClosedImmersion (baseRestriction A π m) :=
  IsClosedImmersion.spec_of_surjective _ (restriction_surjective A π m)

/-- Adjacent arithmetic coefficient thickenings have the same underlying support. -/
instance baseRestriction_surjective : Surjective (baseRestriction A π m) := by
  constructor
  change Function.Surjective (PrimeSpectrum.comap (restriction A π m).toRingHom)
  rw [← Set.range_eq_univ, range_comap_of_surjective _ _ (restriction_surjective A π m)]
  exact (PrimeSpectrum.zeroLocus_eq_univ_iff _).mpr (restriction_kernel_le_nilradical A π m)

/-- The original coefficient inclusion has exactly the last parameter-power kernel. -/
theorem baseRestriction_ker : (baseRestriction A π m).ker =
    baseIdeal (.of (Quotient A π (m + 1)))
      (Ideal.span {parameter A π (m + 1)}) ^ (m + 1) := by
  rw [baseRestriction, specMap_ker_baseIdeal]
  change baseIdeal (.of (Quotient A π (m + 1))) (RingHom.ker (restriction A π m).toRingHom) = _
  rw [restriction_ker, baseIdeal_pow]

variable (n : ℕ) (h : 2 ≤ n)

/-- The actual whole-family restriction is a closed immersion. -/
instance stageRestriction_isClosedImmersion : IsClosedImmersion (stageRestriction A π m n h) :=
  MorphismProperty.of_isPullback (stageRestriction_isPullback A π m n h).flip inferInstance

/-- Adjacent arithmetic families have identical underlying support. -/
instance stageRestriction_surjective : Surjective (stageRestriction A π m n h) :=
  MorphismProperty.of_isPullback (stageRestriction_isPullback A π m n h).flip inferInstance

/-- The original arithmetic parameter ideal extended to the whole stage. -/
def stageParameterIdeal : (family A π m n h).left.IdealSheafData :=
  (baseIdeal (.of (Quotient A π m)) (Ideal.span {parameter A π m})).comap
    (family A π m n h).hom

/-- The original family restriction has precisely the prescribed adic kernel. -/
theorem stageRestriction_ker : (stageRestriction A π m n h).ker =
    stageParameterIdeal A π (m + 1) n h ^ (m + 1) := by
  have he := (stageRestriction_isPullback A π m n h).isoPullback_hom_fst
  rw [← he, Scheme.Hom.ker_comp_of_isIso, ker_fst_of_isClosedImmersion,
    baseRestriction_ker, idealSheaf_comap_pow]
  rfl

/-- The lower arithmetic stage is the actual parameter-power subscheme of the upper stage. -/
def stageRestrictionIdealIso : (family A π m n h).left ≅
    (stageParameterIdeal A π (m + 1) n h ^ (m + 1)).subscheme :=
  asIso (stageRestriction A π m n h).toImage ≪≫
    subschemeCongr (stageRestriction_ker A π m n h)

/-- The ideal-subscheme comparison preserves the original arithmetic restriction morphism. -/
@[reassoc] theorem stageRestrictionIdealIso_hom_ι :
    (stageRestrictionIdealIso A π m n h).hom ≫
      (stageParameterIdeal A π (m + 1) n h ^ (m + 1)).subschemeι =
        stageRestriction A π m n h := by
  rw [stageRestrictionIdealIso, Iso.trans_hom, Category.assoc, subschemeCongr_hom_ι]
  exact Scheme.Hom.toImage_imageι _

end FLT.Mazur.PolygonArithmeticStages
