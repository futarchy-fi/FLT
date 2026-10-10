/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.PolygonStageRetainedNaturality
public import FLT.Mazur.BaseAdicQuotientSpectrum

/-!
# Realizing the original polygon system as actual ideal-power subschemes

The original stages are the closed subschemes cut out by powers of the
extended complete-base parameter ideal. Their original transition maps
become the actual inclusions of those subschemes.
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry

namespace FLT.Mazur.PolygonInfinitesimalStages

set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true

attribute [local irreducible] family boundaryLine boundaryStageRetainedIso
  exactVeroneseTensorReduction

variable (K : Type) [Field K] (n : ℕ) (h : 2 ≤ n) [NeZero n]

/-- The actual extension of the complete-base parameter ideal to the compatible Proj. -/
def compatibleProjAdicIdeal : (exactVeroneseProj K n h).IdealSheafData :=
  (BaseAdicThickening.baseIdeal (.of (PowerSeries K)) (parameterIdeal K)).comap
    (exactVeroneseProjToBase K n h)

/-- The original polygon stage is the actual parameter-power closed subscheme of the candidate. -/
def originalStageAdicIso (m : ℕ) :
    (family K m n h).left ≅ (compatibleProjAdicIdeal K n h ^ (m + 1)).subscheme :=
  boundaryStageRetainedIso K n h m ≪≫
    (exactVeroneseProj_adic_isPullback K n h m).isoPullback ≪≫
      (BaseAdicThickening.quotientPullbackIso (.of (PowerSeries K)) (parameterIdeal K)
        (exactVeroneseProjToBase K n h) (m + 1)).symm

/-- The realization retains the original section-evaluation map into the total candidate. -/
@[reassoc]
theorem originalStageAdicIso_hom_ι (m : ℕ) :
    (originalStageAdicIso K n h m).hom ≫
      (compatibleProjAdicIdeal K n h ^ (m + 1)).subschemeι =
        originalStageToCompatibleProj K n h m := by
  change (originalStageAdicIso K n h m).hom ≫
    (((BaseAdicThickening.baseIdeal (.of (PowerSeries K)) (parameterIdeal K)).comap
      (exactVeroneseProjToBase K n h)) ^ (m + 1)).subschemeι = _
  rw [originalStageAdicIso, Iso.trans_hom, Iso.trans_hom, Iso.symm_hom,
    Category.assoc, Category.assoc,
    ← BaseAdicThickening.quotientPullbackIso_hom_fst, Iso.inv_hom_id_assoc]
  erw [(exactVeroneseProj_adic_isPullback K n h m).isoPullback_hom_fst]
  rfl

/-- Every original stage enters the complete candidate by its actual closed immersion. -/
theorem originalStageToCompatibleProj_isClosedImmersion (m : ℕ) :
    IsClosedImmersion (originalStageToCompatibleProj K n h m) := by
  rw [← originalStageAdicIso_hom_ι]
  infer_instance

/-- Larger parameter powers define larger original infinitesimal neighborhoods. -/
theorem compatibleProjAdicIdeal_power_le {a b : ℕ} (hab : a ≤ b) :
    compatibleProjAdicIdeal K n h ^ (b + 1) ≤ compatibleProjAdicIdeal K n h ^ (a + 1) := by
  intro U
  exact Ideal.pow_le_pow_right (Nat.add_le_add_right hab 1)

/-- The actual transition between the candidate's parameter-power closed subschemes. -/
def compatibleProjAdicInclusion {a b : ℕ} (hab : a ≤ b) :
    (compatibleProjAdicIdeal K n h ^ (a + 1)).subscheme ⟶
      (compatibleProjAdicIdeal K n h ^ (b + 1)).subscheme :=
  Scheme.IdealSheafData.inclusion (compatibleProjAdicIdeal_power_le K n h hab)

/-- All original transitions are the actual ideal-power subscheme inclusions under realization. -/
@[reassoc]
theorem originalStageAdicIso_naturality {a b : ℕ} (f : a ⟶ b) :
    (stageSystem K n h).map f ≫ (originalStageAdicIso K n h b).hom =
      (originalStageAdicIso K n h a).hom ≫
        compatibleProjAdicInclusion K n h (leOfHom f) := by
  apply (cancel_mono (compatibleProjAdicIdeal K n h ^ (b + 1)).subschemeι).mp
  rw [Category.assoc, originalStageAdicIso_hom_ι, Category.assoc,
    compatibleProjAdicInclusion, Scheme.IdealSheafData.inclusion_subschemeι,
    originalStageAdicIso_hom_ι, originalStageToCompatibleProj_naturality]

end FLT.Mazur.PolygonInfinitesimalStages
