/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.AffineSpectrumKernelIdeal
public import FLT.Mazur.PolygonStageClosedImmersion

/-!
# The actual parameter-power ideal of an adjacent polygon stage

The original stage transition has precisely the extended parameter-power
ideal as kernel. Its source is therefore the actual ideal-power subscheme,
with the comparison retaining the given transition morphism.
-/

@[expose] public noncomputable section

open CategoryTheory AlgebraicGeometry

namespace FLT.Mazur.PolygonInfinitesimalStages

open FCurve BaseAdicThickening Scheme.IdealSheafData

set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true

variable (R : Type*) [CommRing R] (m : ℕ)

/-- The actual adjacent ring kernel is the principal last-power ideal. -/
theorem restriction_ker : RingHom.ker (restriction R m).toRingHom =
    Ideal.span {parameter R (m + 1)} ^ (m + 1) := by
  rw [Ideal.span_singleton_pow]
  ext z
  rw [RingHom.mem_ker, Ideal.mem_span_singleton]
  exact (restriction_eq_zero_iff R m z).trans (exists_congr fun _ ↦ eq_comm)

/-- The actual coefficient-spectrum kernel is the last power of its parameter ideal. -/
theorem baseRestriction_ker : (baseRestriction R m).ker =
    baseIdeal (.of (Ring R (m + 1))) (Ideal.span {parameter R (m + 1)}) ^ (m + 1) := by
  rw [baseRestriction, specMap_ker_baseIdeal]
  change baseIdeal (.of (Ring R (m + 1))) (RingHom.ker (restriction R m).toRingHom) = _
  rw [restriction_ker, baseIdeal_pow]

variable (n : ℕ) (h : 2 ≤ n)

/-- The actual coefficient parameter ideal extended to a polygon stage. -/
def stageParameterIdeal : (family R m n h).left.IdealSheafData :=
  (baseIdeal (.of (Ring R m)) (Ideal.span {parameter R m})).comap (family R m n h).hom

/-- The original adjacent transition has exactly the prescribed parameter-power kernel. -/
theorem stageRestriction_ker : (stageRestriction R m n h).ker =
    stageParameterIdeal R (m + 1) n h ^ (m + 1) := by
  rw [← stageRestrictionIso_fst R m n h, Scheme.Hom.ker_comp_of_isIso,
    ker_fst_of_isClosedImmersion, baseRestriction_ker, idealSheaf_comap_pow]
  rfl

/-- The actual lower stage is the parameter-power closed subscheme of the upper stage. -/
def stageRestrictionIdealIso : (family R m n h).left ≅
    (stageParameterIdeal R (m + 1) n h ^ (m + 1)).subscheme :=
  asIso (stageRestriction R m n h).toImage ≪≫ subschemeCongr (stageRestriction_ker R m n h)

/-- The closed-subscheme comparison retains the original adjacent transition. -/
@[reassoc] theorem stageRestrictionIdealIso_hom_ι :
    (stageRestrictionIdealIso R m n h).hom ≫
      (stageParameterIdeal R (m + 1) n h ^ (m + 1)).subschemeι =
        stageRestriction R m n h := by
  rw [stageRestrictionIdealIso, Iso.trans_hom, Category.assoc, subschemeCongr_hom_ι]
  exact Scheme.Hom.toImage_imageι _

end FLT.Mazur.PolygonInfinitesimalStages
