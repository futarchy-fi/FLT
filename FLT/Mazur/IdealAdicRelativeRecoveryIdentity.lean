/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.IdealAdicRelativeAffineRecovery
public import FLT.Mazur.AffineTildeSemilinearCoherence

/-!
# Recovery on the original chart

The identity coefficient restriction is the geometric identity comparison.
Consequently the self-chart recovery is the canonical open-immersion counit
applied to the descended projection.
-/

@[expose] public noncomputable section

set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency.types false

open CategoryTheory AlgebraicGeometry
open Scheme.Modules

universe u

namespace FLT.Mazur.IdealAdicGradedPullback

open ModuleSheafOverlapImageTransition SheafPullbackPathComparison

/-- A coordinate along an identity refinement cancels to the chart counit. -/
lemma coordinateIso_identity {A B : Scheme.{u}} (p : A ⟶ A) (i : A ⟶ B)
    [IsOpenImmersion i] (h : p ≫ i = i) (hp : p = 𝟙 A) (M : A.Modules) :
    (coordinateIso p i i h M).hom ≫
        (pullbackCongr hp).hom.app M ≫ (pullbackId A).hom.app M =
      (openCounitIso i M).hom := by
  subst p
  simp only [pullbackCongr, eqToIso_refl, Iso.refl_hom, NatTrans.id_app, Category.id_comp]
  unfold coordinateIso
  simp only [Iso.trans_hom, Functor.mapIso_hom]
  have hc := comparison_id_comp i ((pushforward i).obj M)
  change (comparison (𝟙 A) i i h).inv.app _ ≫ _ ≫ _ = _
  apply (cancel_epi ((comparison (𝟙 A) i i h).hom.app _)).mp
  simp only [← Category.assoc, Iso.hom_inv_id_app, Category.id_comp]
  rw [hc]
  exact (pullbackId A).hom.naturality (openCounitIso i M).hom

variable {X Y : Scheme.{u}} [IsLocallyNoetherian X] [IsLocallyNoetherian Y] [IsAffine Y]
variable (J : Y.IdealSheafData) (f : X ⟶ Y)

attribute [local instance] relativeTensorChart_isOpenImmersion
attribute [local irreducible] Scheme.Modules.pullback
attribute [local irreducible] relativeDescendedCoefficientSheaf relativeCoefficientSheafMap

/-- The identity coefficient map is the actual geometric identity pullback comparison. -/
lemma relativeCoefficientSheafMap_id (U : X.affineOpens) :
    relativeCoefficientSheafMap J f (𝟙 U.1) =
      (pullbackCongr (relativeTensorTransition_id J f U)).hom.app
          (relativeChartCoefficientSheaf J f U) ≫
        (pullbackId _).hom.app (relativeChartCoefficientSheaf J f U) := by
  apply AffineTildePullbackSectionMap.hom_ext
    (CommRingCat.ofHom (relativeRestriction J f (𝟙 U.1)).toRingHom)
    (relativeChartCoefficient J f U)
  intro m
  refine (relativeCoefficientSheafMap_unit J f (𝟙 U.1) m).trans ?_
  rw [IdealAdicGradedSections.restrict_id, RingHom.id_apply]
  change _ = ((pullbackId _).hom.app (relativeChartCoefficientSheaf J f U)).app ⊤
    (((pullbackCongr (relativeTensorTransition_id J f U)).hom.app
      (relativeChartCoefficientSheaf J f U)).app ⊤
        (((pullbackPushforwardAdjunction (relativeTensorTransition J f (𝟙 U.1))).unit.app
          (relativeChartCoefficientSheaf J f U)).app ⊤
            ((relativeChartCoefficientSectionsIso J f U).hom m)))
  rw [SchemeModulePullbackUnits.congr_unit, SchemeModulePullbackUnits.id_unit]

/-- Self-chart coordinates followed by coefficient recovery are the canonical counit. -/
lemma relativeAffineCoefficientCoordinate_self (U : X.affineOpens) :
    (relativeAffineCoefficientCoordinate J f (𝟙 U.1)).hom ≫
        relativeCoefficientSheafMap J f (𝟙 U.1) =
      (openCounitIso (relativeTensorChart J f U) (relativeChartCoefficientSheaf J f U)).hom := by
  rw [relativeCoefficientSheafMap_id]
  exact coordinateIso_identity (relativeTensorTransition J f (𝟙 U.1))
    (relativeTensorChart J f U) (relativeTensorTransition_chart J f (𝟙 U.1))
    (relativeTensorTransition_id J f U) (relativeChartCoefficientSheaf J f U)

/-- On its own chart, recovery is the descended projection followed by the actual counit. -/
lemma relativeDescendedAffineRecoveryIso_self (U : X.affineOpens) :
    (relativeDescendedAffineRecoveryIso J f (𝟙 U.1)).hom =
      (pullback (relativeTensorChart J f U)).map (relativeDescendedCoefficientProjection J f U) ≫
        (openCounitIso (relativeTensorChart J f U) (relativeChartCoefficientSheaf J f U)).hom := by
  change (_ ≫ _) ≫ _ = _
  rw [Category.assoc, relativeAffineCoefficientCoordinate_self]

end FLT.Mazur.IdealAdicGradedPullback
