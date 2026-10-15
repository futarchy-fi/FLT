/-
Copyright (c) 2026 krandder. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: krandder
-/
module

public import FLT.Mazur.PolygonArithmeticStageNaturality
public import FLT.Mazur.BaseAdicQuotientSpectrum

/-!
# Realizing the original polygon system as actual ideal-power subschemes

The original stages are the closed subschemes cut out by powers of the
extended complete-base parameter ideal. Their original transition maps
become the actual inclusions of those subschemes.
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry

namespace FLT.Mazur.PolygonArithmeticStages

set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true

attribute [local irreducible] family boundaryLine boundaryStageRetainedIso
  exactVeroneseTensorReduction

variable (A : Type) [CommRing A] [IsNoetherianRing A] [IsLocalRing A] [IsDomain A]
  (π : A) (hne : π ≠ 0) (hgen : IsLocalRing.maximalIdeal A = ideal A π) (n : ℕ) (h : 2 ≤ n)
    [NeZero n]

/-- The actual extension of the complete-base parameter ideal to the compatible Proj. -/
def compatibleProjAdicIdeal : (exactVeroneseProj A π n h hne hgen).IdealSheafData :=
  (BaseAdicThickening.baseIdeal (.of A) (ideal A π)).comap
    (exactVeroneseProjToBase A π n h hne hgen)

/-- The original polygon stage is the actual parameter-power closed subscheme of the candidate. -/
def originalStageAdicIso (m : ℕ) :
    (family A π m n h).left ≅ (compatibleProjAdicIdeal A π hne hgen n h ^ (m + 1)).subscheme :=
  boundaryStageRetainedIso A π hne hgen n h m ≪≫
    (exactVeroneseProj_adic_isPullback A π n h hne hgen m).isoPullback ≪≫
      (BaseAdicThickening.quotientPullbackIso (.of A) (ideal A π)
        (exactVeroneseProjToBase A π n h hne hgen) (m + 1)).symm

/-- The realization retains the original section-evaluation map into the total candidate. -/
@[reassoc]
theorem originalStageAdicIso_hom_ι (m : ℕ) :
    (originalStageAdicIso A π hne hgen n h m).hom ≫
      (compatibleProjAdicIdeal A π hne hgen n h ^ (m + 1)).subschemeι =
        originalStageToCompatibleProj A π hne hgen n h m := by
  change (originalStageAdicIso A π hne hgen n h m).hom ≫
    (((BaseAdicThickening.baseIdeal (.of A) (ideal A π)).comap
      (exactVeroneseProjToBase A π n h hne hgen)) ^ (m + 1)).subschemeι = _
  rw [originalStageAdicIso, Iso.trans_hom, Iso.trans_hom, Iso.symm_hom,
    Category.assoc, Category.assoc,
    ← BaseAdicThickening.quotientPullbackIso_hom_fst, Iso.inv_hom_id_assoc]
  erw [(exactVeroneseProj_adic_isPullback A π n h hne hgen m).isoPullback_hom_fst]
  rfl

/-- Larger parameter powers define larger original infinitesimal neighborhoods. -/
theorem compatibleProjAdicIdeal_power_le {a b : ℕ} (hab : a ≤ b) :
    compatibleProjAdicIdeal A π hne hgen n h ^ (b + 1) ≤ compatibleProjAdicIdeal A π hne hgen n h
    ^ (a + 1) := by
  intro U
  exact Ideal.pow_le_pow_right (Nat.add_le_add_right hab 1)

/-- The actual transition between the candidate's parameter-power closed subschemes. -/
def compatibleProjAdicInclusion {a b : ℕ} (hab : a ≤ b) :
    (compatibleProjAdicIdeal A π hne hgen n h ^ (a + 1)).subscheme ⟶
      (compatibleProjAdicIdeal A π hne hgen n h ^ (b + 1)).subscheme :=
  Scheme.IdealSheafData.inclusion (compatibleProjAdicIdeal_power_le A π hne hgen n h hab)

/-- All original transitions are the actual ideal-power subscheme inclusions under realization. -/
@[reassoc]
theorem originalStageAdicIso_naturality {a b : ℕ} (f : a ⟶ b) :
    (stageSystem A π n h).map f ≫ (originalStageAdicIso A π hne hgen n h b).hom =
      (originalStageAdicIso A π hne hgen n h a).hom ≫
        compatibleProjAdicInclusion A π hne hgen n h (leOfHom f) := by
  apply (cancel_mono (compatibleProjAdicIdeal A π hne hgen n h ^ (b + 1)).subschemeι).mp
  rw [Category.assoc, originalStageAdicIso_hom_ι, Category.assoc,
    compatibleProjAdicInclusion, Scheme.IdealSheafData.inclusion_subschemeι,
    originalStageAdicIso_hom_ι, originalStageToCompatibleProj_naturality]

end FLT.Mazur.PolygonArithmeticStages
