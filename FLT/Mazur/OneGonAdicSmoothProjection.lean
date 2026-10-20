/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.OneGonAdicCharacterStructure

/-!
# Finite-stage maps land in the original complete-base smooth open

The original smooth coefficient comparison gives the same map into the cubic
as projection of the original finite Y chart. Thus every constructed finite
map lands in the smooth locus of the original whole-base cubic.
-/

@[expose] public noncomputable section

open CategoryTheory AlgebraicGeometry

namespace FLT.Mazur.OneGonAdicCharacterTower

open OneGonSmoothing WeierstrassIntegralChart WeierstrassDividedDepth

set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true

variable {R G : Type} [CommRing R] [AddCommGroup G] (I : Ideal R) (t : R)
  (ht : t ∈ I) (g : stageSource I G 0 ⟶ stageGroup I t 0)

/-- The actual smooth comparison from each quotient curve to the original complete-base curve. -/
def smoothProjection (m : ℕ) : (stageGroup I t m).X.left ⟶
    (integralSmoothGroup (equation t)).X.left :=
  (eqToHom (congrArg integralSmoothGroup
    (equation_map t (algebraMap R (StageRing I m))).symm)).hom.hom.hom.left ≫
      originalSmoothCoefficientMap (StageRing I m) (equation t)

/-- The chart projection retains its actual factorization through the original smooth open. -/
@[reassoc] theorem chartProjection_inclusion (m : ℕ) :
    chartProjection I t m ≫ integralCurveChart (equation t) 1 =
      (stageChartIso I t ht m).hom ≫ smoothProjection I t m ≫
        (integralSmoothOpen (equation t)).ι := by
  simp only [smoothProjection, Category.assoc, originalSmoothCoefficientMap_inclusion]
  rw [equationTransport_smoothInclusion_assoc
    (equation_map t (algebraMap R (StageRing I m))).symm]
  erw [stageChartIso_hom_inclusion_assoc I t ht m]
  exact chartCoefficientRingMapTo_inclusion (Ideal.Quotient.mk (I ^ (m + 1)))
    (equation t) 1 (equation (parameter I t m)) (equation_map t _)

/-- Each original finite character map retains the full cubic inclusion over the complete base. -/
@[reassoc] theorem towerAffine_inclusion (m : ℕ) :
    towerAffine I t ht g m ≫ integralCurveChart (equation t) 1 =
      (tower I t ht g m).hom.hom.hom.left ≫ smoothProjection I t m ≫
        (integralSmoothOpen (equation t)).ι := by
  rw [towerAffine, Category.assoc, chartProjection_inclusion I t ht m, towerChart_smooth_assoc]

/-- Every point of the finite character source maps into the original whole-base smooth open. -/
theorem towerAffine_range_smooth (m : ℕ) :
    Set.range (towerAffine I t ht g m ≫ integralCurveChart (equation t) 1) ⊆
      integralSmoothOpen (equation t) := by
  rw [towerAffine_inclusion]
  rintro _ ⟨x, rfl⟩
  exact ((smoothProjection I t m) ((tower I t ht g m).hom.hom.hom.left x)).property

end FLT.Mazur.OneGonAdicCharacterTower
